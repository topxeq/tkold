package tk

import "testing"

func Test001(t *testing.T) {
	tmps := EncodeStringUnderline("abcXYZ*^&的技术开发")
	Pl("%v", tmps)

	Pl("%v", DecodeStringUnderline(tmps))

}

func Test002(t *testing.T) {
	tmpList, errT := ParseCommandLine("list -open=`abcXYZ*^&的技术开发` -s='sdf' abc")
	Plvsr(tmpList, errT)

}
