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

func Test003(t *testing.T) {
	buf := []byte("abcABZ%&*&我们大家都很好。")
	Pl("%v", ByteSliceToStringDec(buf, ","))

}
