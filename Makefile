.PHONY: default check mypy
default: check
check: mypy

mypy:
	mypy crltool/