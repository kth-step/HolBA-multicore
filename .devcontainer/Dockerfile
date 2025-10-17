FROM docker.io/hakarlsson/hol:latest
RUN apt update && apt install python3 -y 
RUN cd /hol/examples/l3-machine-code/common && Holmake
RUN cd /hol/examples/l3-machine-code/arm8/model && Holmake
RUN cd /hol/examples/l3-machine-code/arm8/step && Holmake
RUN cd /hol/examples/l3-machine-code/m0/model && Holmake
RUN cd /hol/examples/l3-machine-code/m0/step && Holmake
