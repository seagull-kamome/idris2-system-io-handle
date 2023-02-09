
PKG=system-io-handle
DEPS=-p contrib -p elab-util -p sop
IDRIS2_OPTS+=


build:
	idris2 ${IDRIS2_OPTS} --build ${PKG}.ipkg

install:
	idris2 ${IDRIS2_OPTS} --install ${PKG}.ipkg

clean:
	idris2 --clean ${PKG}.ipkg
	rm -rf build

distclean:
	find . -name *~ -delete
	find . -name *.bak -delete

check: check-chez check-node check-js check-refc
check-chez:
	echo "ABCDE" | idris2 ${IDRIS2_OPTS} ${DEPS} -p ${PKG} tests/Test-System-IO-Terminal.idr --cg chez -x main
check-node:
	echo "ABCDE" | idris2 ${IDRIS2_OPTS} ${DEPS} -p ${PKG} tests/Test-System-IO-Terminal.idr --cg node -x main
check-js:
	# Javascript backend wont support prim__os
	# idris2 -p ${PKG} tests/Test-System-IO-Terminal.idr --cg javascript -o test-javascript.js
	#
check-refc:#
	idris2 ${IDRIS2_OPTS} ${DEPS} -p ${PKG} tests/Test-System-IO-Terminal.idr --cg refc -o test-refc
	echo "ABDE" | build/exec/test-refc

.PHONY: clean deepclean build install check check-local

