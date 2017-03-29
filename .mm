/* 
 * Simple, 32-bit and 64-bit clean allocator based on an explicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"The A-Top Team",
	/* First member's full name */
	"Suthar Kunal Vinaykumar",
	/* First member's email address */
	"201401131@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Piyush Datani",
	/* Second member's email address (leave blank if none) */
	"201401130@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 17)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* Given block ptr bp, compute address of next and previous free blocks. */
#define NEXT_FREEBLKP(bp) (*(char **)(bp + WSIZE))
#define PREV_FREEBLKP(bp) (*(char **)(bp))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */
static char *freelisthead; /*Pointer to the first free block*/
/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_in_freelist(void *bp);/* inserts the block with payload at bp into the free block list */
static void delete_from_freelist(void *bp);/* deletes the block with payload at bp from the free block list */
/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
         freelisthead=heap_listp+DSIZE;
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{ 
    size_t oldsize;
  void *newptr;	
     /* If size == 0 then this is just free, and we return NULL. */
       if(size == 0){ 
        mm_free(ptr); 
        return NULL; 
         } 
       else { 
       oldsize = GET_SIZE(HDRP(ptr)); 
       size += 2 * WSIZE; // 2 words for header and footer
    
       /*if newsize is less than oldsize then we just return bp */
           if(size <= oldsize){
             return ptr; 
            }
      /*if newsize is greater than oldsize */ 
     else { 
   
         // if the next block is free and the coalesced size is greater than the updated size do the coalescing with it 	
            if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && ((oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= size)
           { 
             size_t totalcoalescedsize=((oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr)))));
             delete_from_freelist(NEXT_BLKP(ptr)); 
             PUT(HDRP(ptr), PACK(totalcoalescedsize, 1)); 
             PUT(FTRP(ptr), PACK(totalcoalescedsize, 1)); 
             return ptr; 
           }
           else 
           {  
               newptr = mm_malloc(size); //if the next block is not free then we only have the option to find another adequate free block in the heap 
               place(newptr, size);      // allocate that block with the updated size
               memcpy(newptr, ptr, size); 
               mm_free(ptr); 
               return newptr; 
           } 
       }
   }
    return NULL;

}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)))||(PREV_BLKP(bp)==bp); /* prev_alloc will be 1 if previous is allocated or if previous does not exist i.e. our freed block 
                                                                            * is right in the start and its previous address would not exist and the macro for PREV_BLKP will         
                                                                            * return bp itself and it won't coalesce on the previous side */
  size_t size = GET_SIZE(HDRP(bp));
   
  if (prev_alloc && !next_alloc) {              /*Case 1*/    
    size += GET_SIZE( HDRP(NEXT_BLKP(bp))  );
    delete_from_freelist(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  else if (!prev_alloc && next_alloc) {         /*Case 2*/          
    size += GET_SIZE( HDRP(PREV_BLKP(bp))  );
    bp = PREV_BLKP(bp);
    delete_from_freelist(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
   
  else if (!prev_alloc && !next_alloc) {        /*Case 3*/        
    size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(HDRP(NEXT_BLKP(bp)));
    delete_from_freelist(PREV_BLKP(bp));
    delete_from_freelist(NEXT_BLKP(bp));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  insert_in_freelist(bp);
  return bp;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
   void *bp;
	for (bp = freelisthead; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEBLKP(bp)) //traversing through the free list for an appropriate find 
	{
		if (asize <= (size_t)GET_SIZE(HDRP(bp)))
			return bp;
    	}
        /* No fit was found. */ 
	return NULL; 
  }

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
                delete_from_freelist(bp);
		bp = NEXT_BLKP(bp);
 
                /* splitting the block for the free size remaining */
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
                coalesce(bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
                delete_from_freelist(bp);
	}
}

/* 
 * Requires:
 *   "bp" is the address of a free block.
 *
 * Effects:
 *  inserts a free block in the free list using the LIFO method i.e. a newly inserted 
 *  block would be inserted in the start of the list i.e. it would be the head of the 
 *  free list.  
 */
static void 
insert_in_freelist(void *bp)
{
  NEXT_FREEBLKP(bp)=freelisthead;
  PREV_FREEBLKP(freelisthead)=bp;
  PREV_FREEBLKP(bp)=NULL;
  freelisthead=bp;
}

/* 
 * Requires:
 *   "bp" is the address of a block which was free block.
 *
 * Effects:
 *  It would delete a block from the free list  
 */
static void
delete_from_freelist(void *bp)
{
        if(PREV_FREEBLKP(bp))  // if the block to be deleted has a prev pointer i.e. if it is not the head of the free list.
		NEXT_FREEBLKP(PREV_FREEBLKP(bp)) = NEXT_FREEBLKP(bp);
	else                // if the block to be deleted is the head
		freelisthead = NEXT_FREEBLKP(bp); 
		PREV_FREEBLKP(NEXT_FREEBLKP(bp)) = PREV_FREEBLKP(bp);
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(freelisthead)) != DSIZE ||
	    !GET_ALLOC(HDRP(freelisthead)))
		printf("Bad prologue header\n");
	checkblock(freelisthead);

	for (bp = freelisthead; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");


        /* Checking whether every free block in the free list is marked free */

        for (bp = freelisthead; GET_ALLOC(HDRP(bp))==0; bp = NEXT_FREEBLKP(bp)){

             /* this loop runs till the end of the free list and 
              * would point to the next of the last free block when the loop breaks
              */

             }
 
             /* if the next of the last free block in free list is not NULL,
              * it means that it has not reached the end of the free list 
              * and the above for loop broke down in between.This case is 
              * only possible when the GET_ALLOC(HDRP(bp)) in the for loop 
              * will not be 0.It means every block in the free list is not free */
 
       if((bp)!=NULL)
       printf("Not every block in the free list is marked free\n");
     
        /*Checking whether every contiguous free blocks escaped coalescing  */
        for(bp=freelisthead;GET_ALLOC(HDRP(bp))==0;bp=NEXT_FREEBLKP(bp))
        {
           bool prev_alloc= GET_ALLOC(FTRP(PREV_BLKP(bp)));
           bool next_alloc= GET_ALLOC(HDRP(NEXT_BLKP(bp)));
           if(!prev_alloc||!next_alloc)
           {
           printf("Contiguous free blocks escaped coalescing\n");
           break;
           }
        }


        /*Checking whether every free block lies within the free list or not */
        
        int counter1=0;
        int counter2=0; 
        //Going through all the blocks
        for (bp = heap_listp+DSIZE; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if(!GET_ALLOC(HDRP(bp)))
                counter1++;
	} 
        //Now going through the free list 
          for (bp = freelisthead; GET_ALLOC(HDRP(bp))==0; bp = NEXT_FREEBLKP(bp)){
              if(!GET_ALLOC(HDRP(bp)))
                counter2++;
             }
         if(counter1!=counter2)
         printf("Not every free block lies within the free list\n");
       
       /* Checking whether the pointers in the free blocks point to valid free blocks */

       void *cp=freelisthead; //pointer to traverse in the free list
       for (bp = freelisthead; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if(!GET_ALLOC(HDRP(bp)))
                {
                   if(bp!=cp) 
                  { 
                    printf("All pointers in the free block do not point to valid free blocks\n");
                    break;
                   }
                   else
                   cp=NEXT_FREEBLKP(cp);
                }
	}
       
       /* Checking whether allocated blocks overlap or not */

        for (bp = freelisthead; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		checkblock(bp); // if the header of the block does not match footer,it means there is some overlapping
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
