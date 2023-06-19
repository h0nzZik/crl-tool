# https://stackoverflow.com/a/64068109/6209703
makeFileDir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

TEMP_DIR=${makeFileDir}/.tmp
$(shell mkdir -p ${TEMP_DIR})

.PHONY: default
default: build-imp

IMP_KOMPILED_DIR := ${TEMP_DIR}/build/imp/
IMP_TIMESTAMP := ${IMP_KOMPILED_DIR}/imp-kompiled/timestamp

.PHONY: build-imp
build-imp: ${IMP_TIMESTAMP}

${IMP_TIMESTAMP}: lang/imp/imp.k
	kompile --emit-json --no-prelude --backend haskell --directory ${IMP_KOMPILED_DIR} $<

.PHONY: imp-run-count
imp-run-count: lang/imp/count.imp ${IMP_TIMESTAMP}
	time krun --directory ${IMP_KOMPILED_DIR} $<

.PHONY: test-imp
test-imp: ${IMP_TIMESTAMP}
	crl-tool --definition ${IMP_KOMPILED_DIR}/imp-kompiled/ prove --specification ./lang/imp/incr_monotonic-spec.k --depth 10
#	crl-tool --definition ${IMP_KOMPILED_DIR}/imp-kompiled prove --specification lang/imp/count_monotonic.json

.PHONY: test-simplify
test-simplify: ${IMP_TIMESTAMP}
	crl-tool --definition ${IMP_KOMPILED_DIR}/imp-kompiled simplify --pattern one_plus_two.kore


.PHONY: clean
clean:
	rm -rf ${TEMP_DIR}

