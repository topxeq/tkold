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

func Test004(t *testing.T) {
	encS := EncryptStringByTXDEF("abcABZ%&*&我们大家都很好。", "")
	Pl("enc: %v", encS)
	decS := DecryptStringByTXDEF(encS, "")
	Pl("dec: %v", decS)

	encS = EncryptStringByTXDEF("abcABZ%&*&我们大家都很好。", "abcd")
	Pl("enc: %v", encS)
	decS = DecryptStringByTXDEF(encS, "abcd")
	Pl("dec: %v", decS)

	decS = DecryptStringByTXDEF("63BF6D952E585B5E3E3D5724272927E98D94E9C2B5ECADB2F2B9C3F894CCF6D19DF8BAD4FC979B", "abcd")
	Pl("decabcd: %v", decS)

}
