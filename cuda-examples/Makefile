NVCC = nvcc

NVCCFLAGS += -use_fast_math \
		-arch=sm_61 \
		-lm \
		--expt-extended-lambda \
		$(SPACE)

EXECUTABLE := vec_add

CUFILE := vec_add_cuda.cu

OBJS = vec_add_cuda.o

all : $(EXECUTABLE)

.c.o :
	$(NVCC) $(NVCCFLAGS)  -o $@ -c $<

%.o:	%.cu
	$(NVCC)  $(NVCCFLAGS) -o $@ -c $<


$(EXECUTABLE) : $(OBJS)
	$(NVCC) $(NVCCFLAGS) -o $@  $?

clean:
	rm -f $(EXECUTABLE) $(OBJS) *.linkinfo