package tk

import "testing"

func Test001(t *testing.T) {
	tmps := EncodeStringUnderline("abcXYZ*^&的技术开发")
	Pl("%v", tmps)

	Pl("%v", DecodeStringUnderline(tmps))

}
