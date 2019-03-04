.PHONY: all
all: makedir proverif vampire narrator pvatp

.PHONY: clean
clean:
	rm -rf build/

install: all
	sudo cp    build/pvatp        /usr/local/bin/
	sudo cp -r build/pvatp_assets /usr/local/bin/

makedir:
	mkdir -p build
	mkdir -p build/pvatp_assets

proverif: makedir
	cd proverif2.00; ./build
	cp proverif2.00/proverif build/pvatp_assets/

vampire_tar:
	if [ ! -f "4.2.2.tar.gz" ]; then \
		wget https://github.com/vprover/vampire/archive/4.2.2.tar.gz; \
		tar xfz 4.2.2.tar.gz; \
		fi

vampire: makedir vampire_tar
	cd vampire-4.2.2; make vampire
	cp vampire-4.2.2/vampire build/pvatp_assets/

narrator: makedir
	cd narrator; make
	rm -rf build/pvatp_assets/narrator/
	mkdir -p build/pvatp_assets/narrator/
	cp -r narrator/_build/default/src/* build/pvatp_assets/narrator/

pvatp: makedir
	cp src/pvatp.py build/pvatp

