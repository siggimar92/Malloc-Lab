/*
 * mm-freelist.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*Macros and values B&H Fig 10.45*/

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define OVERHEAD 8

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(size_t *) (p))
#define PUT(p, val) (*(size_t *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//#define HDRP(ptr) (char *)(ptr)
//#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - DSIZE)))

#define NEXT_FREE(bp) ((char *)(bp) + WSIZE)

#define GET_NXT_PTR(p) ((char *)(p) + DSIZE)
#define GET_PREV_PTR(p) ((char*)(p) + WSIZE)

void* heap_listp; /* pointer to the heap */
void* root_ptr; /*pointer to header of first free block*/
static void* extend_heap(size_t words);
static void* find_fit(size_t asize);
static void* place(void* bp, size_t asize);
static void* coalesce(void* ptr);
static int in_heap(const void *p);
static int aligned(const void* p);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0); /* alignment */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1)); /* Prologue Header */
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1)); /* Prologue Footer */
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));  /* Epilogue Header */
    heap_listp += DSIZE;
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)//try to extend heap
        return -1;
    //root_ptr = heap_listp+WSIZE; -> taken care of in extend_heap
    
    
    (int *)(*(heap_listp+(DSIZE/4))) = NULL; //set prev to null
    (int *)(*(heap_listp+((DSIZE+WSIZE)/4))) = NULL; //set next to null
    
    //(void *)(&heap_listp+DSIZE) = NULL;/*prev ptr*/
    //(heap_listp+WSIZE+DSIZE) = NULL;/*nxt ptr*/
    return 0;
}

/*
 * malloc
 * success: return a pointer to memory block of at least size bytes.
 * fail: return NULL, set errno
 */
void *malloc (size_t size) {
   size_t asize;
    size_t extend_size;
    char* ptr;
    
    if (size <= 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    
    if ((ptr = find_fit(size)) != NULL)
    {
        place(ptr, asize);
        return ptr;
    }
    
    extend_size = MAX(asize,CHUNKSIZE);
    if ((ptr = extend_heap(extend_size/WSIZE)) == NULL)
        return NULL;
    place(ptr, asize);
    return ptr;
}

/*
 * free
 * return block pointed at by p to pool of available memory
 * p must come from malloc() or realloc()
 */
void free (void *bp) {
    
    if(!bp) return;
    
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));//mark as free
    PUT(FTRP(bp), PACK(size, 0));
    PUT((int *)bp, NULL);//set prev to null
    PUT(NEXT_FREE(bp), root_ptr);//set next to root
    root_ptr = HDRP(bp);//set root to this block
            
   //coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 * changes size of block p and returns pointed to new block
 * contents of new block unchanged up to min of old and new size
 * old block has been freed
 */
void *realloc(void *oldptr, size_t size) {
  size_t oldSize;
  size_t asize;
  size_t diffSize;
  
  if(oldptr == NULL)
    return malloc(size);
  if(size == 0){
    free(oldptr);
    return NULL;
  }
  /*how to check that it was returned by
   *a previous call to {m|re|c}alloc? */
  oldSize = GET_SIZE(HDRP(oldptr));
  
  if(size <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1))/DSIZE);
  
  if(asize == oldSize) return oldptr;

  if(asize < oldSize){

    PUT(HDRP(oldptr), PACK(asize,1));
    PUT(HDRP(oldptr)+asize-(WSIZE), PACK(asize,1));
    
    PUT(NEXT_BLKP(oldptr), PACK((oldSize-asize), 0)); /*set header for freed space*/
    PUT((NEXT_BLKP(oldptr)+GET_SIZE(HDRP(NEXT_BLKP(oldptr))) - WSIZE), PACK((oldSize-asize),0));
    coalesce(NEXT_BLKP(oldptr)+WSIZE);
    return oldptr;
  
  }
  
  /*In Case there's enough free space next to the block to simply extend the allocated space*/
  if(!GET_ALLOC(NEXT_BLKP(oldptr)) && (((oldSize + GET_SIZE(HDRP(NEXT_BLKP(oldptr))))) <= asize)){
    diffSize = GET_SIZE(HDRP(NEXT_BLKP(oldptr))) - asize; /*left over free block space after allocated space is extended*/
    PUT(HDRP(oldptr), PACK(asize,1));
    PUT(HDRP(oldptr)+asize-(WSIZE), PACK(asize,1));
    if(diffSize > 0){This password is used by project owners and members when checking out or committing source code changes, or when using command-line tools to upload f
      PUT(NEXT_BLKP(oldptr), PACK(diffSize, 0));/*set header of shrunken free space*/
      PUT(NEXT_BLKP(oldptr)+diffSize-(WSIZE), PACK(diffSize, 0)); /*set footer of shrunken free space*/
    }
    return oldptr;
  }

  /*Allocated Space needs to be moved to another locale */
  return place(oldptr, asize);
      
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.This password is used by project owners and members when checking out or committing source code changes, or when using command-line tools to upload f
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

static void* extend_heap(size_t words)
{
    char * ptr;
    size_t size;
    
    /* allocates even number of words */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((int)(ptr = mem_sbrk(size)) < 0)
        return NULL;
    
    /* initialize free block header/footer */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    PUT((int *)GET_NEXT_PTR(HDRP(ptr)), root_ptr);
    PUT((int *)GET_PREV_PTR(HDRP(ptr)), NULL);
    root_ptr = HDRP(ptr);
    
    return ptr;
    //coalesce(ptr);
}

static void *coalesce(void * ptr)
{
    size_t prev = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (prev && next)
        return ptr;
    
    else if (prev && !next)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptPUT(GET_NEXT_PTR(root_ptr)r), PACK(size, 0));
        return (ptr);
    }
    
    else if (!prev && next)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        return (PREV_BLKP(ptr));
    }
    
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        return (PREV_BLKP(ptr));
    }
}

/* performs first-fit search of implicit free list, returns pointer to first fit or null if none found */
static void* find_fit(size_t asize)
{
  void* p;
  /*checks to make sure size fits alignment*/
  if(asize <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((asize + (OVERHEAD) + (DSIZE-1))/DSIZE);

  p = root_ptr; /*set pointer to the beginning of the first header in the list*/

  /*runs until reaches the epilogue block*/
  while(p != NULL){
    if((GET_SIZE(p) >= asize)) return p;
    p = (p+DSIZE); /*set p to point to next block*/
  }
  return NULL;
}

/*places the requested block at beginning of free block, spliiting if necessary
 * bp points to the beginning of the header, NOT the payload
*/
static void * place(void* bp, size_t asize)
{
  void* prevptr;
  void* nxtptr;
  size_t diffSize;
  /*assumes asize is already aligned*/
  size_t freeBlockSize = GET_SIZE(bp);
  if(((diffSize = freeBlockSize-asize)) < (2*(DSIZE))){ /*allocate whole block*/
    PUT(bp, PACK((freeBlockSize+asize), 1));
    PUT((bp+(freeBlockSize+asize-WSIZE)), PACK((freeBlockSize+asize),1));
    prevptr = (void *)(bp+WSIZE);
    nxtptr = (void *)(bp+DSIZE);
    if(prevptr == NULL){
      if(nxtptr == NULL){
    root_ptr = NULL;
    return (void *)(bp+WSIZE);
      }
      root_ptr = nxtpr;
      return (void *)(bp+WSIZE);
    }
    (void *)(prevptr + DSIZE) = nxtptr;
    (void *)(nxtptr + WSIZE) = prevptr;
    return (void *)(bp+WSIZE);
  }
  PUT(bp, PACK(asize,1));
  PUT((bp+asize-WSIZE), PACK(asize,1));
  /*set header and footer for newly split free block*/
  PUT(bp+asize, PACK(diffSize,0));
  PUT((bp+asize+diffSize-WSIZE), PACK(diffsize,0));
  prevptr = (void *)(bp+WSIZE);
  nxtptr = (void *)(bp+DSIZE);
  if(prevptr == NULL){
    if(nxtptr == NULL){
      root_ptr = (void *)(bp+asize);
      (void *)(bp+asize+WSIZE) = NULL;
      (void *)(bp+asize+DSIZE) = NULL;
      return (void *)(bp+WSIZE);
    }
    root_ptr = (void *)(bp+asize);
    (void *)(bp+freeBlockSize+WSIZE) = (bp+asize);
    (void *)(bp+asize+WSIZE) = NULL;
    (void *)(bp+asize+DSIZE) = nxtptr;
    return (void *)(bp+WSIZE);
  }
  
  (void *)(prevptr + DSIZE) = (bp+asize);
  (void *)(nxtptr + WSIZE) = (bp+asize);
  (void *)(bp+asize+WSIZE) = prevptr;
  (void *)(bp+asize+DSIZE) = nxtptr;
  return (void *)(bp+WSIZE);
  
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
}