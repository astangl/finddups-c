/* finddups - recursively search for duplicate files in one or more specified directories
 *            Can help deduplication efforts.
 *
 * Copyright 2012, Alex Stangl
 * License: OpenBSD/ISC.  See file LICENSE for full text of license.
 */

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <ftw.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <sys/stat.h>

/*@-exitarg@*/

/* buffer size default value; override when compiling with -DBUFSIZE=... */
#if !defined(BUFSIZE)
#define BUFSIZE 1024
#endif

/* change DEBUG to 1 on next line to enable debug printing */
#define DEBUG 0

#if DEBUG
#define DEBUG_PRINT(...) printf(__VA_ARGS__)
#else
#define DEBUG_PRINT(...)
#endif

#define EX_USAGE 64

struct fe {const char *name; struct fe *next; dev_t dev; ino_t inode;};
struct dupNode {long size; struct fe *files; struct dupNode *next;};
struct Node {long size,c; struct fe *files; struct Node *left, *right;int color;} *root;

void error_exit(char *errorMsg, const char *parm)
{
	char *msg = errorMsg;
	if (parm) {
		msg = malloc(strlen(errorMsg) + strlen(parm) + 1);
		strcpy(msg, errorMsg);
		strcat(msg, parm);
	}

	syslog(LOG_USER, msg);
	if (parm)
		free(msg);

	exit(1);
}

static void *Malloc(size_t bytes)
{
	void *retval = malloc(bytes);
	if (retval == 0)
		exit(2);
	return retval;
}

static char *copystr(const char *from)
{
	size_t l = strlen(from);
	char *retval = Malloc((l+1) * sizeof(char));
	strcpy(retval, from);
	return retval;
}

static int isRed(struct Node *n) {
	return n != NULL && n->color;
}

static void colorFlip(struct Node *n) {
	assert(n->color == 0);
	assert(n->left->color == 1);
	assert(n->right->color == 1);
	n->color = 1;
	n->left->color = n->right->color = 0;
}

static struct Node *rotateLeft(struct Node *h) {
	struct Node *x = h->right;
	h->right = x->left;
	x->left = h;
	x->color = h->color;
	h->color = 1;
	return x;
}

static struct Node *rotateRight(struct Node *h) {
	struct Node *x = h->left;
	h->left = x->right;
	x->right = h;
	x->color = h->color;
	h->color = 1;
	return x;
}

static struct fe *newFileNode(const char *name, const struct stat *st)
{
	struct fe *retval = malloc(sizeof (struct fe));
	retval->name = copystr(name);
	retval->next = NULL;
	retval->dev = st->st_dev;
	retval->inode = st->st_ino;
	return retval;
}

static struct fe *copyFileNode(struct fe *old)
{
	struct fe *retval = malloc(sizeof (struct fe));
	retval->name = copystr(old->name);
	retval->next = NULL;
	retval->dev = old->dev;
	retval->inode = old->inode;
	return retval;
}


/* recursive insert called during traversal
 * can optimize later by putting *name and *st into globals
 */
static struct Node *insertR(struct Node *node, const char *name, const struct stat *st)
{
	struct fe *fp;
	if (!node) {
		node = malloc(sizeof (struct Node));
		node->size = st->st_size;
		node->c = 1;
		node->left = node->right = NULL;
		node->files = newFileNode(name, st);
		node->color = 1;
	} else if (st->st_size == node->size) {
		/* traverse file list to see if we have same dev/inode as an existing file (e.g., hard link)
		 * if so, just return existing node unmodified (no need to add this redundant file)
		 */
		for (fp = node->files; fp; fp=fp->next) {
			if (fp->dev == st->st_dev && fp->inode == st->st_ino)
				return node;
		}
		fp = newFileNode(name, st);
		fp->next = node->files;
		node->files = fp;
	} else {
		if (isRed(node->left) && isRed(node->right))
			colorFlip(node);

		if (st->st_size < node->size) {
			node->left = insertR(node->left, name, st);
		} else {
			node->right = insertR(node->right, name, st);
		}

		if (isRed(node->right) && !isRed(node->left))
			node = rotateLeft(node);

		if (isRed(node->left) && isRed(node->left->left))
			node = rotateRight(node);
	}
	return node;
}

/* main entry point for insert, inserting at root */
static void insert(const char *name, const struct stat *st) {
	/*
	DEBUG_PRINT("Inserting %s with size %ld\n", name, st->st_size);
	*/
	root = insertR(root, name, st);
	root->color = 0;
}

static int visit(const char *name, const struct stat *st, int flag, struct FTW *ftw) {
	/*
	DEBUG_PRINT("name = %s, flag = %d, st = %ld\n", name, flag, st);
	DEBUG_PRINT("visiting %s with size %ld\n", name, st->st_size);
	*/
	if (flag == FTW_F) 
		insert(name, st);
	return 0;
}

static struct dupNode *addDupNode(int size, struct fe *file, struct dupNode *retval) {
	struct fe *fp = copyFileNode(file);
	if (!retval) {
		retval = malloc(sizeof (struct dupNode));
		retval->size = size;
		retval->files = NULL;
		retval->next = NULL;
	}
	fp->next = retval->files;
	retval->files = fp;
	return retval;
}

/* return possibly-null chain of duplicates, based on scanning files in
 * specified (sub)tree and possibly-null existing chain
 * should free all nodes, and file entries, except those returned
 */
static struct dupNode *chkForDups(struct Node *node, struct dupNode *retval) {
	int cnt, i, j, fdi, fdj, nri, nrj, *fflags, pr;
	struct fe *fp, *fi, *fj;
	struct dupNode *dn = 0, *pn = 0;
	long *ar, ari, arj, maxToSkip;
	char *ibuff, *jbuff;
	off_t lsi, lsj;
	if (node) {

		/* do left subbranch, then process this node, then right subbranch
		 * this way chain gets built up so that it starts with largest first
		 */
		retval = chkForDups(node->left, retval);

		/* check for duplicates in this current node. First, degenerate cases:
		 * If less than 2 files, then no dups
		 * else if size == 0, all considered dups
		 */
		/* DEBUG_PRINT("Checking dups of size %ld\n", node->size); */
		for (cnt=0, fp = node->files; fp != NULL; fp = fp->next, ++cnt);
		if (cnt < 2) {
			/* free all file entries */
			for (fp = node->files; fp != NULL; fp = fp->next)
				free(fp);
		} else {
			/* TODO If general case handles size == 0 case efficiently, get rid
			 *     of this special case
			 */
			if (node->size) {
				ibuff = Malloc(BUFSIZE);
				jbuff = Malloc(BUFSIZE);
				fflags = calloc(cnt, sizeof(int));
				/* General case, two or more non-empty files.
				 * allocate N x N array for bookkeeping to keep track of how
				 * many blocks files A and B have in common
				 */
				ar = calloc(cnt * cnt, sizeof(long));
				for (i = 0, fi = node->files; i < cnt - 1; ++i, fi = fi->next) {
					/* DEBUG_PRINT("i = %d, file = %s, fflags[i] = %d\n", i, fi->name, fflags[i]); */
					if (fflags[i])
						continue;      /* i already output as a dup */

					for (j = i + 1, fj = fi->next; fj; ++j, fj = fj->next) {
						/* DEBUG_PRINT("j = %d, file = %s, fflags[j] = %d\n", j, fj->name, fflags[j]); */
						if (fflags[j])
							continue;  /* j already output as a dup */

						/* Look in past rows of ar at column values for i & j.
						 * If any rows have diff. values for these, we infer they don't match.
						 * Otherwise, find max value for these in the prev. rows.
						 * We know that these many blocks for the 2 files are identical, so
						 * we can skip those.
						 */
						maxToSkip = 0;
						/* DEBUG_PRINT("i = %d, cnt = %d\n", i, cnt); */
						for (pr = 0; pr < i; ++pr) {
							ari = ar[pr*cnt + i];
							/* DEBUG_PRINT("ar[%d] = %ld, ar[%d] = %ld\n", pr*cnt + i, ari, pr*cnt + j, ar[pr*cnt + j]); */
							if (ari != ar[pr*cnt + j]) {
								DEBUG_PRINT("Skipping comparison of %s and %s because of prefix length diff\n",
										fi->name, fj->name);
								maxToSkip = -1;
								break;
							}
							if (ari > maxToSkip)
								maxToSkip = ari;
						}

						/* DEBUG_PRINT("maxToSkip = %ld\n", maxToSkip); */

						if (maxToSkip < 0)
							continue;         /* inferred these differ due to prefix length differences */

						/* TODO  optimize open/closing of fi, maybe use a rewind */
						if ((fdi = open(fi->name, O_RDONLY)) < 0) {
							printf("Error opening %s\n", fi->name);
							error_exit("Error opening ", fi->name);
						}

						/* error_exit("Error opening ", fi->name); */
						if ((fdj = open(fj->name, O_RDONLY)) < 0)
							error_exit("Error opening ", fj->name);

						if (maxToSkip > 0) {
							DEBUG_PRINT("Skipping ahead %ld in %s and %s because of prefix inferences\n",
									maxToSkip, fi->name, fj->name);
							lsi = lseek(fdi, maxToSkip, SEEK_SET);
							lsj = lseek(fdj, maxToSkip, SEEK_SET);
							if (lsi < 0 || lsj < 0) {
								free(ibuff);
								free(jbuff);
								free(fflags);
								free(ar);
								close(fdj);
								close(fdi);
								error_exit("Error seeking in ",
									lsi < 0 ? fi->name : fj->name);
							}
						}

						for (;;) {
							nri = read(fdi, ibuff, BUFSIZE);
							nrj = read(fdj, jbuff, BUFSIZE);
							if (nri < 0 || nrj < 0) {
								free(ibuff);
								free(jbuff);
								free(fflags);
								free(ar);
								close(fdj);
								close(fdi);
								error_exit("Error reading ",
									nri < 0 ? fi->name : fj->name);
							}

							/* check for files being diff, by length or by value */
							if (nri != nrj)
								break;

							if (memcmp(ibuff, jbuff, nri))
								break;

							/* custom memcmp so we know where mismatch occurred */

							/* note that we've successfully compared another block */
							ar[i*cnt + j] += nri;
							/* DEBUG_PRINT("ar[%d] = %ld\n", i*cnt + j, ar[i*cnt + j]); */

							/* if we've reached end of file, these are dups */
							if (!nri) {
								/* DEBUG_PRINT("We found dups!\n"); */
								/* make sure we only add fi once */
								if (! fflags[i])
									dn = addDupNode(node->size, fi, dn);
								dn = addDupNode(node->size, fj, dn);
								fflags[i] = fflags[j] = 1;
								/* DEBUG_PRINT("setting fflags[%d] and fflags[%d]\n", i, j); */
								break;
							}
						}
						close(fdj);
						close(fdi);
					}

					/* If we created a chain of dups of fi, then add this to the chain of dups & reset */
					if (dn) {
						dn->next = retval;
						retval = dn;
						dn = 0;
					}
				}
				free(ibuff);
				free(jbuff);
				free(fflags);
				free(ar);
			} else {
				/* size == 0, so we trivially consider them all dups */
				dn = malloc(sizeof (struct dupNode));
				dn->size = 0;
				dn->files = node->files;
				dn->next = retval;
				retval = dn;
			}
		}

		/* we can only have duplicates if this node has more than 1 file */

		/*
		for (fp = node->files; fp; fp=fp->next)
			DEBUG_PRINT("Checking for duplicate in file %s of size %ld\n", fp->name, node->size);
		*/
		retval = chkForDups(node->right, retval);

		free(node);
	}
	return retval;
}

int main(int argc, char **argv)
{
	int i, j;
	struct dupNode *dups;
	struct fe *fp;

	if (argc < 1) {
		fprintf(stderr, "usage: finddups dir1 [dir2 ... [dirN]]");
		exit(EX_USAGE);
	}

	for (i = 1; i < argc; ++i) {
		j = nftw(argv[i], visit, 64, FTW_PHYS);
		if (j == -1) {
			DEBUG_PRINT("returned %d, errno = %d\n", j, errno);
		}
	}

	DEBUG_PRINT("Done scanning directory tree. Now starting duplicate checks.\n");

	for (dups = chkForDups(root, NULL); dups; dups = dups->next) {
		printf("duplicates of size %ld\n", dups->size);
		for (fp = dups->files; fp; fp = fp->next) {
			printf("%s\n", fp->name);
		}
	}
	return 0;
}

