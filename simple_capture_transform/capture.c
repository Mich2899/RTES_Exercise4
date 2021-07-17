/*
 *
 *  Adapted by Sam Siewert for use with UVC web cameras and Bt878 frame
 *  grabber NTSC cameras to acquire digital video from a source,
 *  time-stamp each frame acquired, save to a PGM or PPM file.
 *
 *  The original code adapted was open source from V4L2 API and had the
 *  following use and incorporation policy:
 * 
 *  This program can be used and distributed without restrictions.
 *
 *      This program is provided with the V4L2 API
 * see http://linuxtv.org/docs.php for more information
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <getopt.h>             /* getopt_long() */

#include <fcntl.h>              /* low-level i/o */
#include <unistd.h>
#include <errno.h>
#include <syslog.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>

#include <linux/videodev2.h>

#include <time.h>

#define CLEAR(x) memset(&(x), 0, sizeof(x))

#define HRES 640
#define VRES 480
#define HRES_STR "640"
#define VRES_STR "480"

//#define HRES 320
//#define VRES 240
//#define HRES_STR "320"
//#define VRES_STR "240"

#define START_UP_FRAMES (8)
#define LAST_FRAMES (1)
#define CAPTURE_FRAMES (1800+LAST_FRAMES)
#define FRAMES_TO_ACQUIRE (CAPTURE_FRAMES + START_UP_FRAMES + LAST_FRAMES)

//#define FRAMES_PER_SEC (1) 
//#define FRAMES_PER_SEC (10) 
//#define FRAMES_PER_SEC (20) 
//#define FRAMES_PER_SEC (25) 
#define FRAMES_PER_SEC (30) 

#define COLOR_CONVERT_RGB
#define DUMP_FRAMES
#define STORE_TRANSFORMED_IMAGE
#define DO_TRANSFORM
//#define STORE_ORIGINAL_IMAGE
//#define STORE_CAPTURED_IMAGE

// Format is used by a number of functions, so made as a file global
static struct v4l2_format fmt;

enum io_method 
{
        IO_METHOD_READ,
        IO_METHOD_MMAP,
        IO_METHOD_USERPTR,
};

struct buffer 
{
        void   *start;
        size_t  length;
};

static char            *dev_name;
//static enum io_method   io = IO_METHOD_USERPTR;
//static enum io_method   io = IO_METHOD_READ;
static enum io_method   io = IO_METHOD_MMAP;
static int              fd = -1;
struct buffer          *buffers;
static unsigned int     n_buffers;
static int              out_buf;
static int              force_format=1;

static int              frame_count = (FRAMES_TO_ACQUIRE);


static double fnow=0.0, fstart=0.0, fstop=0.0;
static struct timespec time_now, time_start, time_stop;

//transform analysis variables
static double trans_start=0.0, trans_stop=0.0, trans_diff=0.0, trans_avg=0.0;
static struct timespec trans_time_start, trans_time_stop;

//acquisition analysis variables
static double acq_start=0.0, acq_stop=0.0, acq_diff=0.0, acq_avg=0.0;
static struct timespec acq_time_start, acq_time_stop;

//write-back analysis variables
static double wb_start=0.0, wb_stop=0.0, wb_diff=0.0, wb_avg=0.0;
static struct timespec wb_time_start, wb_time_stop;

//analysis for part 5b transform+write_back
static double trans_and_wb_start=0.0, trans_and_wb_stop=0.0, trans_and_wb_diff=0.0, trans_and_wb_avg=0.0;
static struct timespec trans_and_wb_time_start, trans_and_wb_time_stop;


//analysis for part 5b original image write back which is rgb
static double orig_start=0.0, orig_stop=0.0, orig_diff=0.0, orig_avg=0.0;
static struct timespec orig_time_start, orig_time_stop;


//analysis for part 5b captured image write back which is YUYV
static double cap_start=0.0, cap_stop=0.0,cap_diff=0.0, cap_avg=0.0;
static struct timespec cap_time_start, cap_time_stop;


static void errno_exit(const char *s)
{
        fprintf(stderr, "%s error %d, %s\n", s, errno, strerror(errno));
        exit(EXIT_FAILURE);
}

static int xioctl(int fh, int request, void *arg)
{
        int r;

        do 
        {
            r = ioctl(fh, request, arg);

        } while (-1 == r && EINTR == errno);

        return r;
}

int frame_check, dump_check;

char ppm_header[]="P6\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char ppm_dumpname[]="frames/test0000.ppm";

char ppm_org_dumpname[]="frames/orgtest0000.ppm";

static void dump_ppm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, i, total, dumpfd;

    if(frame_check==0){
    snprintf(&ppm_dumpname[11], 9, "%04d", tag);
    strncat(&ppm_dumpname[15], ".ppm", 5);
    dumpfd = open(ppm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);
   }

    else if(frame_check==1){
    snprintf(&ppm_org_dumpname[14], 9, "%04d", tag);
    strncat(&ppm_org_dumpname[18], ".ppm", 5);
    dumpfd = open(ppm_org_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);
    }
    
    snprintf(&ppm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&ppm_header[14], " sec ", 5);
    snprintf(&ppm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&ppm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);
   
    // subtract 1 from sizeof header because it includes the null terminator for the string
    written=write(dumpfd, ppm_header, sizeof(ppm_header)-1);

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    clock_gettime(CLOCK_MONOTONIC, &time_now);
    fnow = (double)time_now.tv_sec + (double)time_now.tv_nsec / 1000000000.0;
//    printf("Frame written to flash at %lf, %d, bytes\n", (fnow-fstart), total);
    syslog(LOG_CRIT, "Frame written to flash at %lf, %d, bytes\n", (fnow-fstart), total);

    close(dumpfd);
    
}


char pgm_header[]="P5\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char pgm_dumpname[]="frames/test0000.pgm";

static void dump_pgm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, i, total, dumpfd;
   
    snprintf(&pgm_dumpname[11], 9, "%04d", tag);
    strncat(&pgm_dumpname[15], ".pgm", 5);
    dumpfd = open(pgm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&pgm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&pgm_header[14], " sec ", 5);
    snprintf(&pgm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&pgm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);

    // subtract 1 from sizeof header because it includes the null terminator for the string
    written=write(dumpfd, pgm_header, sizeof(pgm_header)-1);

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    clock_gettime(CLOCK_MONOTONIC, &time_now);
    fnow = (double)time_now.tv_sec + (double)time_now.tv_nsec / 1000000000.0;
//    printf("Frame written to flash at %lf, %d, bytes\n", (fnow-fstart), total);
     syslog(LOG_CRIT, "Frame written to flash at %lf, %d, bytes\n", (fnow-fstart), total);

    close(dumpfd);
    
}


void yuv2rgb_float(float y, float u, float v, 
                   unsigned char *r, unsigned char *g, unsigned char *b)
{
    float r_temp, g_temp, b_temp;

    // R = 1.164(Y-16) + 1.1596(V-128)
    r_temp = 1.164*(y-16.0) + 1.1596*(v-128.0);  
    *r = r_temp > 255.0 ? 255 : (r_temp < 0.0 ? 0 : (unsigned char)r_temp);

    // G = 1.164(Y-16) - 0.813*(V-128) - 0.391*(U-128)
    g_temp = 1.164*(y-16.0) - 0.813*(v-128.0) - 0.391*(u-128.0);
    *g = g_temp > 255.0 ? 255 : (g_temp < 0.0 ? 0 : (unsigned char)g_temp);

    // B = 1.164*(Y-16) + 2.018*(U-128)
    b_temp = 1.164*(y-16.0) + 2.018*(u-128.0);
    *b = b_temp > 255.0 ? 255 : (b_temp < 0.0 ? 0 : (unsigned char)b_temp);
}


// This is probably the most acceptable conversion from camera YUYV to RGB
//
// Wikipedia has a good discussion on the details of various conversions and cites good references:
// http://en.wikipedia.org/wiki/YUV
//
// Also http://www.fourcc.org/yuv.php
//
// What's not clear without knowing more about the camera in question is how often U & V are sampled compared
// to Y.
//
// E.g. YUV444, which is equivalent to RGB, where both require 3 bytes for each pixel
//      YUV422, which we assume here, where there are 2 bytes for each pixel, with two Y samples for one U & V,
//              or as the name implies, 4Y and 2 UV pairs
//      YUV420, where for every 4 Ys, there is a single UV pair, 1.5 bytes for each pixel or 36 bytes for 24 pixels

void yuv2rgb(int y, int u, int v, unsigned char *r, unsigned char *g, unsigned char *b)
{
   int r1, g1, b1;

   // replaces floating point coefficients
   int c = y-16, d = u - 128, e = v - 128;       

   // Conversion that avoids floating point
   r1 = (298 * c           + 409 * e + 128) >> 8;
   g1 = (298 * c - 100 * d - 208 * e + 128) >> 8;
   b1 = (298 * c + 516 * d           + 128) >> 8;

   // Computed values may need clipping.
   if (r1 > 255) r1 = 255;
   if (g1 > 255) g1 = 255;
   if (b1 > 255) b1 = 255;

   if (r1 < 0) r1 = 0;
   if (g1 < 0) g1 = 0;
   if (b1 < 0) b1 = 0;

   *r = r1 ;
   *g = g1 ;
   *b = b1 ;
}

void convert_to_negative(unsigned char *r, unsigned char *g, unsigned char *b, unsigned char *nr, unsigned char *ng, unsigned char *nb)
{
	*nr = 255 - *r;
	*ng = 255 - *g;
	*nb = 255 - *b;
}

// always ignore first 8 frames
int framecnt=-8;

unsigned char bigbuffer[(1280*960)];
unsigned char negbuffer[(1280*960)];

static void process_image(const void *p, int size)
{

    int i, newi, newsize=0;
    struct timespec frame_time;
    int y_temp, y2_temp, u_temp, v_temp;
    unsigned char *pptr = (unsigned char *)p;

    // record when process was called
    clock_gettime(CLOCK_REALTIME, &frame_time);    

    framecnt++;
//    syslog(LOG_CRIT,"Processing started!!\n");
//    syslog(LOG_CRIT,"Wait for magic to happen in approximately 3 minutes!!");
//    printf("frame %d: ", framecnt);
     syslog(LOG_CRIT, "frame %d: ", framecnt);
    
    if(framecnt == 0) 
    {
        clock_gettime(CLOCK_MONOTONIC, &time_start);
        fstart = (double)time_start.tv_sec + (double)time_start.tv_nsec / 1000000000.0;
    }

#ifdef DUMP_FRAMES	

    // This just dumps the frame to a file now, but you could replace with whatever image
    // processing you wish.
    //

    if(fmt.fmt.pix.pixelformat == V4L2_PIX_FMT_GREY)
    {
        //printf("Dump graymap as-is size %d\n", size);
        syslog(LOG_CRIT, "Dump graymap as-is size %d\n", size);
        dump_pgm(p, size, framecnt, &frame_time);
    }

    else if(fmt.fmt.pix.pixelformat == V4L2_PIX_FMT_YUYV)
    {

    //to analyse the frame rate for transformation + write back
    clock_gettime(CLOCK_MONOTONIC, &trans_and_wb_time_start);
    trans_and_wb_start = (double)trans_and_wb_time_start.tv_sec + (double)trans_and_wb_time_start.tv_nsec/1000000000.0;


    //to analyse the frame rate for captured image write back (YUYV)
    clock_gettime(CLOCK_MONOTONIC, &cap_time_start);
    cap_start = (double)cap_time_start.tv_sec + (double)cap_time_start.tv_nsec/1000000000.0;


    //to analyse the frame rate for original image write back (RGB)
    clock_gettime(CLOCK_MONOTONIC, &orig_time_start);
    orig_start = (double)orig_time_start.tv_sec + (double)orig_time_start.tv_nsec/1000000000.0;

    //to analyse the frame rate for just transformation
    clock_gettime(CLOCK_MONOTONIC, &trans_time_start);
    trans_start = (double)trans_time_start.tv_sec + (double)trans_time_start.tv_nsec/1000000000.0;

#if defined(COLOR_CONVERT_RGB)
       
        // Pixels are YU and YV alternating, so YUYV which is 4 bytes
        // We want RGB, so RGBRGB which is 6 bytes
        //
        for(i=0, newi=0; i<size; i=i+4, newi=newi+6)
        {
            y_temp=(int)pptr[i]; u_temp=(int)pptr[i+1]; y2_temp=(int)pptr[i+2]; v_temp=(int)pptr[i+3];
            yuv2rgb(y_temp, u_temp, v_temp, &bigbuffer[newi], &bigbuffer[newi+1], &bigbuffer[newi+2]);
	    yuv2rgb(y2_temp, u_temp, v_temp, &bigbuffer[newi+3], &bigbuffer[newi+4], &bigbuffer[newi+5]);
	}

#if defined(DO_TRANSFORM)	    
	for(i=0, newi=0; i<size; i=i+4, newi=newi+6)
	{
          convert_to_negative(&bigbuffer[newi], &bigbuffer[newi+1], &bigbuffer[newi+2], &negbuffer[newi], &negbuffer[newi+1], &negbuffer[newi+2]);
          convert_to_negative(&bigbuffer[newi+3], &bigbuffer[newi+4], &bigbuffer[newi+5], &negbuffer[newi+3], &negbuffer[newi+4], &negbuffer[newi+5]);
	}
#endif
	//to find transform avg frame rate
	clock_gettime(CLOCK_MONOTONIC, &trans_time_stop);
	trans_stop = (double)trans_time_stop.tv_sec + (double)trans_time_stop.tv_nsec/1000000000.0;

	trans_diff =trans_stop - trans_start;
	trans_avg =trans_avg +trans_diff;


#if defined(STORE_TRANSFORMED_IMAGE)

       //to find write back avg frame rate
       clock_gettime(CLOCK_MONOTONIC, &wb_time_start);
       wb_start= (double)wb_time_start.tv_sec + (double)wb_time_start.tv_nsec/1000000000.0;
       if(framecnt > -1)
       {
         frame_check=0;
	 dump_ppm(negbuffer, ((size*6)/4), framecnt, &frame_time);
	 syslog(LOG_CRIT, "Transformed image dumped size %d\n", size);
       }

       clock_gettime(CLOCK_MONOTONIC, &wb_time_stop);
       wb_stop = (double)wb_time_stop.tv_sec + (double)wb_time_stop.tv_nsec/1000000000.0;

       wb_diff=wb_stop-wb_start;
       wb_avg=wb_avg+wb_diff;


       //to find transform+wb avg frame rate
       clock_gettime(CLOCK_MONOTONIC, &trans_and_wb_time_stop);
       trans_and_wb_stop = (double)trans_and_wb_time_stop.tv_sec + (double)trans_and_wb_time_stop.tv_nsec/1000000000.0;

       trans_and_wb_diff = trans_and_wb_stop - trans_and_wb_start;
       trans_and_wb_avg = trans_and_wb_avg + trans_and_wb_diff;

#endif

#if defined(STORE_ORIGINAL_IMAGE)
       if(framecnt > -1) 
       {
	    frame_check=1;
            dump_ppm(bigbuffer, ((size*6)/4), framecnt, &frame_time);
            //printf("Dump YUYV converted to RGB size %d\n", size);
	    syslog(LOG_CRIT, "Original image dumped size %d\n", size);
       }

	clock_gettime(CLOCK_MONOTONIC, &orig_time_stop);
	orig_stop = (double)orig_time_stop.tv_sec + (double)orig_time_stop.tv_nsec/1000000000.0;

	orig_diff = orig_stop - orig_start;
	orig_avg = orig_avg + orig_diff;

#endif

#if defined(STORE_CAPTURED_IMAGE)      
        // Pixels are YU and YV alternating, so YUYV which is 4 bytes
        // We want Y, so YY which is 2 bytes
	//
        for(i=0, newi=0; i<size; i=i+4, newi=newi+2)
        {
            // Y1=first byte and Y2=third byte
            bigbuffer[newi]=pptr[i];
            bigbuffer[newi+1]=pptr[i+2];
        }

        if(framecnt > -1)
        {
            dump_pgm(bigbuffer, (size/2), framecnt, &frame_time);
            syslog(LOG_CRIT, "Captured image stored with size %d\n", size);
	}

	
	clock_gettime(CLOCK_MONOTONIC, &cap_time_stop);
	cap_stop = (double)cap_time_stop.tv_sec + (double)cap_time_stop.tv_nsec/1000000000.0;

	cap_diff = cap_stop - cap_start;
	cap_avg = cap_avg + cap_diff;

#endif

#else
      
        // Pixels are YU and YV alternating, so YUYV which is 4 bytes
        // We want Y, so YY which is 2 bytes
	//
        for(i=0, newi=0; i<size; i=i+4, newi=newi+2)
        {
            // Y1=first byte and Y2=third byte
            bigbuffer[newi]=pptr[i];
            bigbuffer[newi+1]=pptr[i+2];
        }

        if(framecnt > -1)
        {
            dump_pgm(bigbuffer, (size/2), framecnt, &frame_time);
            //printf("Dump YUYV converted to YY size %d\n", size);
            syslog(LOG_CRIT, "Dump YUYV converted to YY size %d\n", size);
        }
#endif

    }

    else if(fmt.fmt.pix.pixelformat == V4L2_PIX_FMT_RGB24)
    {
        //printf("Dump RGB as-is size %d\n", size);
        syslog(LOG_CRIT, "Dump RGB as-is size %d\n", size);
        dump_ppm(p, size, framecnt, &frame_time);
    }
    else
    {
        //printf("ERROR - unknown dump format\n");
        syslog(LOG_CRIT, "ERROR - unknown dump format\n");
    }

#endif
}


static int read_frame(void)
{
    struct v4l2_buffer buf;
    unsigned int i;

//    clock_gettime(CLOCK_MONOTONIC, &acq_time_start);
//    acq_start= (double)acq_time_start.tv_sec + (double)acq_time_start.tv_nsec/1000000000.0;

    switch (io)
    {

        case IO_METHOD_READ:
            if (-1 == read(fd, buffers[0].start, buffers[0].length))
            {
                switch (errno)
                {

                    case EAGAIN:
                        return 0;

                    case EIO:
                        /* Could ignore EIO, see spec. */

                        /* fall through */

                    default:
                        errno_exit("read");
                }
            }

            process_image(buffers[0].start, buffers[0].length);
            break;

        case IO_METHOD_MMAP:
	    clock_gettime(CLOCK_MONOTONIC,&acq_time_start);
	    acq_start = (double)acq_time_start.tv_sec + (double)acq_time_start.tv_nsec/1000000000.0;
            CLEAR(buf);

            buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
            buf.memory = V4L2_MEMORY_MMAP;

            if (-1 == xioctl(fd, VIDIOC_DQBUF, &buf))
            {
                switch (errno)
                {
                    case EAGAIN:
                        return 0;

                    case EIO:
                        /* Could ignore EIO, but drivers should only set for serious errors, although some set for
                           non-fatal errors too.
                         */
                        return 0;


                    default:
                        //printf("mmap failure\n");
                        syslog(LOG_CRIT, "mmap failure\n");
                        errno_exit("VIDIOC_DQBUF");
                }
            }

            assert(buf.index < n_buffers);

	    clock_gettime(CLOCK_MONOTONIC, &acq_time_stop);
	    acq_stop= (double)acq_time_stop.tv_sec + (double)acq_time_stop.tv_nsec/1000000000.0;

	    acq_diff = acq_stop-acq_start;
	    acq_avg = acq_avg + acq_diff;

            process_image(buffers[buf.index].start, buf.bytesused);

            if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                    errno_exit("VIDIOC_QBUF");
            break;

        case IO_METHOD_USERPTR:
            CLEAR(buf);

            buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
            buf.memory = V4L2_MEMORY_USERPTR;

            if (-1 == xioctl(fd, VIDIOC_DQBUF, &buf))
            {
                switch (errno)
                {
                    case EAGAIN:
                        return 0;

                    case EIO:
                        /* Could ignore EIO, see spec. */

                        /* fall through */

                    default:
                        errno_exit("VIDIOC_DQBUF");
                }
            }

            for (i = 0; i < n_buffers; ++i)
                    if (buf.m.userptr == (unsigned long)buffers[i].start
                        && buf.length == buffers[i].length)
                            break;

            assert(i < n_buffers);

            process_image((void *)buf.m.userptr, buf.bytesused);

            if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                    errno_exit("VIDIOC_QBUF");
            break;
    }


//    clock_gettime(CLOCK_MONOTONIC, &acq_time_stop);
//    acq_stop= (double)acq_time_stop.tv_sec + (double)acq_time_stop.tv_nsec/1000000000.0;

//    acq_diff = acq_stop - acq_start;
//    acq_avg  = acq_avg + acq_diff;
    //printf("R");
    //syslog(LOG_CRIT, "R");
    return 1;
}


static void mainloop(void)
{
    unsigned int count;
    struct timespec read_delay;
    struct timespec time_error;

    // Replace this with a delay designed for your rate
    // of frame acquitision and storage.
    //
  
#if (FRAMES_PER_SEC  == 1)
    //printf("Running at 1 frame/sec\n");
    syslog(LOG_CRIT, "Running at 1 frame/sec\n");
    read_delay.tv_sec=1;
    read_delay.tv_nsec=0;
#elif (FRAMES_PER_SEC == 10)
    //printf("Running at 10 frames/sec\n");
    syslog(LOG_CRIT, "Running at 10 frames/sec\n");
    read_delay.tv_sec=0;
    read_delay.tv_nsec=100000000;
#elif (FRAMES_PER_SEC == 20)
    //printf("Running at 20 frames/sec\n");
    syslog(LOG_CRIT, "Running at 20 frames/sec\n");
    read_delay.tv_sec=0;
    read_delay.tv_nsec=49625000;
#elif (FRAMES_PER_SEC == 25)
    //printf("Running at 25 frames/sec\n");
    syslog(LOG_CRIT, "Running at 25 frames/sec\n");
    read_delay.tv_sec=0;
    read_delay.tv_nsec=39625000;
#elif (FRAMES_PER_SEC == 30)
    //printf("Running at 30 frames/sec\n");
    syslog(LOG_CRIT, "Running at 30 frames/sec\n");
    read_delay.tv_sec=0;
    read_delay.tv_nsec=33333333;
#else
    //printf("Running at 1 frame/sec\n");
    syslog(LOG_CRIT, "Running at 1 frame/sec\n");
    read_delay.tv_sec=1;
    read_delay.tv_nsec=0;
#endif

    count = frame_count;

    while (count > 0)
    {
        for (;;)
        {
            fd_set fds;
            struct timeval tv;
            int r;

            FD_ZERO(&fds);
            FD_SET(fd, &fds);

            /* Timeout. */
            tv.tv_sec = 2;
            tv.tv_usec = 0;

            r = select(fd + 1, &fds, NULL, NULL, &tv);

            if (-1 == r)
            {
                if (EINTR == errno)
                    continue;
                errno_exit("select");
            }

            if (0 == r)
            {
                fprintf(stderr, "select timeout\n");
                exit(EXIT_FAILURE);
            }

            if (read_frame())
            {
                if(nanosleep(&read_delay, &time_error) != 0)
                    perror("nanosleep");
                else
		{
		    if(framecnt > 1)
	            {	
		        clock_gettime(CLOCK_MONOTONIC, &time_now);
		        fnow = (double)time_now.tv_sec + (double)time_now.tv_nsec / 1000000000.0;
                        //printf(" read at %lf, @ %lf FPS\n", (fnow-fstart), (double)(framecnt+1) / (fnow-fstart));
                        syslog(LOG_CRIT, " read at %lf, @ %lf FPS\n", (fnow-fstart), (double)(framecnt+1) / (fnow-fstart));
		    }
		    else 
		    {
                        //printf("at %lf\n", fnow);
                        syslog(LOG_CRIT, "at %lf\n", fnow);
		    }
		}

                count--;
                break;
            }

            /* EAGAIN - continue select loop unless count done. */
            if(count <= 0) break;
        }

        if(count <= 0) break;
    }

    clock_gettime(CLOCK_MONOTONIC, &time_stop);
    fstop = (double)time_stop.tv_sec + (double)time_stop.tv_nsec / 1000000000.0;

}

static void stop_capturing(void)
{
        enum v4l2_buf_type type;

        switch (io) {
        case IO_METHOD_READ:
                /* Nothing to do. */
                break;

        case IO_METHOD_MMAP:
        case IO_METHOD_USERPTR:
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMOFF, &type))
                        errno_exit("VIDIOC_STREAMOFF");
                break;
        }
}

static void start_capturing(void)
{
        unsigned int i;
        enum v4l2_buf_type type;

        switch (io) 
        {

        case IO_METHOD_READ:
                /* Nothing to do. */
                break;

        case IO_METHOD_MMAP:
                for (i = 0; i < n_buffers; ++i) 
                {
                        //printf("allocated buffer %d\n", i);
                        syslog(LOG_CRIT, "allocated buffer %d\n", i);
                        struct v4l2_buffer buf;

                        CLEAR(buf);
                        buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                        buf.memory = V4L2_MEMORY_MMAP;
                        buf.index = i;

                        if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                                errno_exit("VIDIOC_QBUF");
                }
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMON, &type))
                        errno_exit("VIDIOC_STREAMON");
                break;

        case IO_METHOD_USERPTR:
                for (i = 0; i < n_buffers; ++i) {
                        struct v4l2_buffer buf;

                        CLEAR(buf);
                        buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                        buf.memory = V4L2_MEMORY_USERPTR;
                        buf.index = i;
                        buf.m.userptr = (unsigned long)buffers[i].start;
                        buf.length = buffers[i].length;

                        if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                                errno_exit("VIDIOC_QBUF");
                }
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMON, &type))
                        errno_exit("VIDIOC_STREAMON");
                break;
        }
}

static void uninit_device(void)
{
        unsigned int i;

        switch (io) {
        case IO_METHOD_READ:
                free(buffers[0].start);
                break;

        case IO_METHOD_MMAP:
                for (i = 0; i < n_buffers; ++i)
                        if (-1 == munmap(buffers[i].start, buffers[i].length))
                                errno_exit("munmap");
                break;

        case IO_METHOD_USERPTR:
                for (i = 0; i < n_buffers; ++i)
                        free(buffers[i].start);
                break;
        }

        free(buffers);
}

static void init_read(unsigned int buffer_size)
{
        buffers = calloc(1, sizeof(*buffers));

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        buffers[0].length = buffer_size;
        buffers[0].start = malloc(buffer_size);

        if (!buffers[0].start) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }
}

static void init_mmap(void)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count = 6;
        req.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_MMAP;

        if (-1 == xioctl(fd, VIDIOC_REQBUFS, &req)) 
        {
                if (EINVAL == errno) 
                {
                        fprintf(stderr, "%s does not support "
                                 "memory mapping\n", dev_name);
                        exit(EXIT_FAILURE);
                } else 
                {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        if (req.count < 2) 
        {
                fprintf(stderr, "Insufficient buffer memory on %s\n", dev_name);
                exit(EXIT_FAILURE);
        }

        buffers = calloc(req.count, sizeof(*buffers));

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < req.count; ++n_buffers) {
                struct v4l2_buffer buf;

                CLEAR(buf);

                buf.type        = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                buf.memory      = V4L2_MEMORY_MMAP;
                buf.index       = n_buffers;

                if (-1 == xioctl(fd, VIDIOC_QUERYBUF, &buf))
                        errno_exit("VIDIOC_QUERYBUF");

                buffers[n_buffers].length = buf.length;
                buffers[n_buffers].start =
                        mmap(NULL /* start anywhere */,
                              buf.length,
                              PROT_READ | PROT_WRITE /* required */,
                              MAP_SHARED /* recommended */,
                              fd, buf.m.offset);

                if (MAP_FAILED == buffers[n_buffers].start)
                        errno_exit("mmap");
        }
}

static void init_userp(unsigned int buffer_size)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count  = 4;
        req.type   = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_USERPTR;

        if (-1 == xioctl(fd, VIDIOC_REQBUFS, &req)) {
                if (EINVAL == errno) {
                        fprintf(stderr, "%s does not support "
                                 "user pointer i/o\n", dev_name);
                        exit(EXIT_FAILURE);
                } else {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        buffers = calloc(4, sizeof(*buffers));

        if (!buffers) {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < 4; ++n_buffers) {
                buffers[n_buffers].length = buffer_size;
                buffers[n_buffers].start = malloc(buffer_size);

                if (!buffers[n_buffers].start) {
                        fprintf(stderr, "Out of memory\n");
                        exit(EXIT_FAILURE);
                }
        }
}

static void init_device(void)
{
    struct v4l2_capability cap;
    struct v4l2_cropcap cropcap;
    struct v4l2_crop crop;
    unsigned int min;

    if (-1 == xioctl(fd, VIDIOC_QUERYCAP, &cap))
    {
        if (EINVAL == errno) {
            fprintf(stderr, "%s is no V4L2 device\n",
                     dev_name);
            exit(EXIT_FAILURE);
        }
        else
        {
                errno_exit("VIDIOC_QUERYCAP");
        }
    }

    if (!(cap.capabilities & V4L2_CAP_VIDEO_CAPTURE))
    {
        fprintf(stderr, "%s is no video capture device\n",
                 dev_name);
        exit(EXIT_FAILURE);
    }

    switch (io)
    {
        case IO_METHOD_READ:
            if (!(cap.capabilities & V4L2_CAP_READWRITE))
            {
                fprintf(stderr, "%s does not support read i/o\n",
                         dev_name);
                exit(EXIT_FAILURE);
            }
            break;

        case IO_METHOD_MMAP:
        case IO_METHOD_USERPTR:
            if (!(cap.capabilities & V4L2_CAP_STREAMING))
            {
                fprintf(stderr, "%s does not support streaming i/o\n",
                         dev_name);
                exit(EXIT_FAILURE);
            }
            break;
    }


    /* Select video input, video standard and tune here. */


    CLEAR(cropcap);

    cropcap.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (0 == xioctl(fd, VIDIOC_CROPCAP, &cropcap))
    {
        crop.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        crop.c = cropcap.defrect; /* reset to default */

        if (-1 == xioctl(fd, VIDIOC_S_CROP, &crop))
        {
            switch (errno)
            {
                case EINVAL:
                    /* Cropping not supported. */
                    break;
                default:
                    /* Errors ignored. */
                        break;
            }
        }

    }
    else
    {
        /* Errors ignored. */
    }


    CLEAR(fmt);

    fmt.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (force_format)
    {
        //printf("FORCING FORMAT\n");
        syslog(LOG_CRIT, "FORCING FORMAT\n");
        fmt.fmt.pix.width       = HRES;
        fmt.fmt.pix.height      = VRES;

        // Specify the Pixel Coding Formate here

        // This one works for Logitech C200
       fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_YUYV;

        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_UYVY;
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_VYUY;

        // Would be nice if camera supported
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_GREY;
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_RGB24;

        //fmt.fmt.pix.field       = V4L2_FIELD_INTERLACED;
        fmt.fmt.pix.field       = V4L2_FIELD_NONE;

        if (-1 == xioctl(fd, VIDIOC_S_FMT, &fmt))
                errno_exit("VIDIOC_S_FMT");

        /* Note VIDIOC_S_FMT may change width and height. */
    }
    else
    {
        //printf("ASSUMING FORMAT\n");
        syslog(LOG_CRIT, "ASSUMING FORMAT\n");
        /* Preserve original settings as set by v4l2-ctl for example */
        if (-1 == xioctl(fd, VIDIOC_G_FMT, &fmt))
                    errno_exit("VIDIOC_G_FMT");
    }

    /* Buggy driver paranoia. */
    min = fmt.fmt.pix.width * 2;
    if (fmt.fmt.pix.bytesperline < min)
            fmt.fmt.pix.bytesperline = min;
    min = fmt.fmt.pix.bytesperline * fmt.fmt.pix.height;
    if (fmt.fmt.pix.sizeimage < min)
            fmt.fmt.pix.sizeimage = min;

    switch (io)
    {
        case IO_METHOD_READ:
            init_read(fmt.fmt.pix.sizeimage);
            break;

        case IO_METHOD_MMAP:
            init_mmap();
            break;

        case IO_METHOD_USERPTR:
            init_userp(fmt.fmt.pix.sizeimage);
            break;
    }
}


static void close_device(void)
{
        if (-1 == close(fd))
                errno_exit("close");

        fd = -1;
}

static void open_device(void)
{
        struct stat st;

        if (-1 == stat(dev_name, &st)) {
                fprintf(stderr, "Cannot identify '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }

        if (!S_ISCHR(st.st_mode)) {
                fprintf(stderr, "%s is no device\n", dev_name);
                exit(EXIT_FAILURE);
        }

        fd = open(dev_name, O_RDWR /* required */ | O_NONBLOCK, 0);

        if (-1 == fd) {
                fprintf(stderr, "Cannot open '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }
}

static void usage(FILE *fp, int argc, char **argv)
{
        fprintf(fp,
                 "Usage: %s [options]\n\n"
                 "Version 1.3\n"
                 "Options:\n"
                 "-d | --device name   Video device name [%s]\n"
                 "-h | --help          Print this message\n"
                 "-m | --mmap          Use memory mapped buffers [default]\n"
                 "-r | --read          Use read() calls\n"
                 "-u | --userp         Use application allocated buffers\n"
                 "-o | --output        Outputs stream to stdout\n"
                 "-f | --format        Force format to 640x480 GREY\n"
                 "-c | --count         Number of frames to grab [%i]\n"
                 "",
                 argv[0], dev_name, frame_count);
}

static const char short_options[] = "d:hmruofc:";

static const struct option
long_options[] = {
        { "device", required_argument, NULL, 'd' },
        { "help",   no_argument,       NULL, 'h' },
        { "mmap",   no_argument,       NULL, 'm' },
        { "read",   no_argument,       NULL, 'r' },
        { "userp",  no_argument,       NULL, 'u' },
        { "output", no_argument,       NULL, 'o' },
        { "format", no_argument,       NULL, 'f' },
        { "count",  required_argument, NULL, 'c' },
        { 0, 0, 0, 0 }
};

int main(int argc, char **argv)
{
    if(argc > 1)
        dev_name = argv[1];
    else
        dev_name = "/dev/video0";


    for (;;)
    {
        int idx;
        int c;

        c = getopt_long(argc, argv,
                    short_options, long_options, &idx);

        if (-1 == c)
            break;

        switch (c)
        {
            case 0: /* getopt_long() flag */
                break;

            case 'd':
                dev_name = optarg;
                break;

            case 'h':
                usage(stdout, argc, argv);
                exit(EXIT_SUCCESS);

            case 'm':
                io = IO_METHOD_MMAP;
                break;

            case 'r':
                io = IO_METHOD_READ;
                break;

            case 'u':
                io = IO_METHOD_USERPTR;
                break;

            case 'o':
                out_buf++;
                break;

            case 'f':
                force_format++;
                break;

            case 'c':
                errno = 0;
                frame_count = strtol(optarg, NULL, 0);
                if (errno)
                        errno_exit(optarg);
                break;

            default:
                usage(stderr, argc, argv);
                exit(EXIT_FAILURE);
        }
    }

    // initialization of V4L2
    open_device();
    init_device();

    start_capturing();


    syslog(LOG_CRIT,"Processing started!!\n");
    syslog(LOG_CRIT,"Wait for magic to happen in approximately 3 minutes!!");
    // service loop frame read
    mainloop();

    // shutdown of frame acquisition service
    stop_capturing();

    //printf("Total capture time=%lf, for %d frames, %lf FPS\n", (fstop-fstart), CAPTURE_FRAMES+1, ((double)CAPTURE_FRAMES / (fstop-fstart)));
    syslog(LOG_CRIT, "Total capture time=%lf, for %d frames, %lf FPS\n", (fstop-fstart), CAPTURE_FRAMES+1, ((double)CAPTURE_FRAMES / (fstop-fstart)));

#if defined(DO_TRANSFORM)
    //average transform processing time = total time taken for transform process/ total number of frames
    syslog(LOG_CRIT, "average transform processing time: %lf\n", (trans_avg/ (double)CAPTURE_FRAMES));
	

   //acquisition frame rate
    syslog(LOG_CRIT, "overall average acquisition frame rate: %lf FPS\n", ((double)CAPTURE_FRAMES/acq_avg));

    //transform frame rate
    syslog(LOG_CRIT, "overall average transform frame rate: %lf FPS\n", ((double)CAPTURE_FRAMES/trans_avg));

#if defined(STORE_TRANSFORMED_IMAGE)
    //write-back frame rate
    syslog(LOG_CRIT, "overall average write-back frame rate: %lf FPS\n", ((double)CAPTURE_FRAMES/wb_avg));

    //transformed and write-back total average frame rate
    syslog(LOG_CRIT, "overall average transform and write-back frame rate: %lf FPS\n",((double)CAPTURE_FRAMES/trans_and_wb_avg));    
    syslog(LOG_CRIT, "acq_avg: %lf trans_avg: %lf wb_avg: %lf\n", acq_avg, (trans_avg/ (double)CAPTURE_FRAMES), (wb_avg/ (double)CAPTURE_FRAMES));

#endif

#endif 

#if defined(STORE_CAPTURED_IMAGE)

    //acquisition frame rate
    syslog(LOG_CRIT, "captured and not transfomed plus write-back : %lf FPS\n", ((double)CAPTURE_FRAMES/cap_avg));
#endif


#if defined(STORE_ORIGINAL_IMAGE)

    //acquisition frame rate
    syslog(LOG_CRIT, "no transform but original(rgb) acquisition frame rate: %lf FPS\n", ((double)CAPTURE_FRAMES/orig_avg));
#endif

//    syslog(LOG_CRIT, "acq_avg: %lf trans_avg: %lf wb_avg: %lf\n", acq_avg, (trans_avg/ (double)CAPTURE_FRAMES), (wb_avg/ (double)CAPTURE_FRAMES));

    uninit_device();
    close_device();
    fprintf(stderr, "\n");
    return 0;
}
