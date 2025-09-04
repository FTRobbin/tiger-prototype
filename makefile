CPPFLAGS = -O2 -Wno-unused-result

json2egraph:
	g++ $(CPPFLAGS) json2egraph.cpp -o json2egraph

main:
	g++ $(CPPFLAGS) main.cpp -o main

clean: 
	rm json2egraph main

all: json2egraph main
