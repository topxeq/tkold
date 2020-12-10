package tk

// build 2020121001

import (
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/md5"
	"database/sql"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"encoding/xml"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"math"
	"math/big"
	"math/rand"
	"net"
	"net/http"
	"net/http/cookiejar"
	"net/smtp"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unsafe"

	"github.com/topxeq/regexpx"
	"github.com/topxeq/tk"
	"github.com/topxeq/xmlx"

	"github.com/aarzilli/sandblast"
	"github.com/melbahja/goph"
	"golang.org/x/crypto/ssh"
	"golang.org/x/crypto/ssh/terminal"
	"golang.org/x/net/html"

	"github.com/atotto/clipboard"
	"github.com/beevik/etree"
	jsoniter "github.com/json-iterator/go"
	uuid "github.com/satori/go.uuid"
	"github.com/topxeq/mahonia"
	"github.com/topxeq/socks"
)

// 类型 types structs

type ExitCallback func()

// 自定义集合类型

type TXCollection struct {
	Content map[string]int
}

func CreateTXCollection(sizeA int) *TXCollection {
	rs := &TXCollection{}
	rs.Content = make(map[string]int, sizeA)

	return rs
}

func (p *TXCollection) InitX(sizeA int) {
	p.Content = make(map[string]int, sizeA)
}

func (p *TXCollection) Length() int {
	if p.Content == nil {
		return 0
	}

	return len(p.Content)
}

func (p *TXCollection) Size() int {
	return p.Length()
}

func (p *TXCollection) AddOrSet(strA string) {
	p.Content[strA] = 1
}

func (p *TXCollection) AddOrSetExcludeEmpty(strA string) {
	if strA == "" {
		return
	}

	p.Content[strA] = 1
}

func (p *TXCollection) Contains(strA string) bool {
	_, ok := p.Content[strA]

	return ok
}

func (p *TXCollection) Remove(strA string) bool {
	_, ok := p.Content[strA]

	if ok {
		delete(p.Content, strA)
		return true
	}

	return false
}

func (p *TXCollection) GetList() []string {
	if (p == nil) || (p.Content == nil) {
		return make([]string, 0)
	}

	rs := make([]string, 0, len(p.Content))

	for k := range p.Content {
		rs = append(rs, k)
	}

	return rs
}

func (p *TXCollection) GetSortedList(ifUpA bool) []string {
	rs := p.GetList()

	if ifUpA {
		sort.Sort(sort.StringSlice(rs))
	} else {
		sort.Sort(sort.Reverse(sort.StringSlice(rs)))
	}

	return rs
}

func (p *TXCollection) GetListString(ifUpA bool, sepA string) string {
	rs := p.GetList()

	if ifUpA {
		sort.Sort(sort.StringSlice(rs))
	} else {
		sort.Sort(sort.Reverse(sort.StringSlice(rs)))
	}

	return strings.Join(rs, sepA)
}

// 存放TX格式的网络API返回结果
type TXResult struct {
	Status  string
	Value   string
	Object  string
	Object2 string
	Object3 string
	Token   string
}

var invalidTXResultG = TXResult{Status: "fail", Value: "invalid response"}

func TXResultFromStringE(strA string) (*TXResult, error) {
	p := new(TXResult)

	errT := json.Unmarshal([]byte(strA), p)

	if errT != nil {
		return nil, errT
	}

	return p, nil
}

func TXResultFromString(strA string) *TXResult {
	p := new(TXResult)

	errT := json.Unmarshal([]byte(strA), p)

	if errT != nil {
		return nil
	}

	return p
}

func TXResultFromStringSafely(strA string) *TXResult {
	p := new(TXResult)

	errT := json.Unmarshal([]byte(strA), p)

	if errT != nil {
		return &invalidTXResultG
	}

	return p
}

// 全局变量 global variables

var logFileG = "c:\\tk.log"
var TimeFormat = "2006-01-02 15:04:05"
var TimeFormatMS = "2006-01-02 15:04:05.000"
var TimeFormatCompact = "20060102150405"
var TimeFormatCompact2 = "2006/01/02 15:04:05"
var GlobalEnvSetG *TXCollection = nil

var variableG = make(map[string]interface{})

var varMutexG sync.Mutex
var fileVarMutexG sync.Mutex

// 全局环境集合相关 global environment related

func SetGlobalEnv(vA string) {
	if GlobalEnvSetG == nil {
		GlobalEnvSetG = CreateTXCollection(100)
	}

	GlobalEnvSetG.AddOrSetExcludeEmpty(vA)
}

func RemoveGlobalEnv(vA string) {
	if GlobalEnvSetG == nil {
		GlobalEnvSetG = CreateTXCollection(100)
	}

	GlobalEnvSetG.Remove(vA)
}

func GetGlobalEnvList() []string {
	if GlobalEnvSetG == nil {
		GlobalEnvSetG = CreateTXCollection(100)
	}

	return GlobalEnvSetG.GetList()
}

func GetGlobalEnvString() string {
	if GlobalEnvSetG == nil {
		GlobalEnvSetG = CreateTXCollection(100)
	}

	return GlobalEnvSetG.GetListString(true, ",")
}

func HasGlobalEnv(vA string) bool {
	if GlobalEnvSetG == nil {
		GlobalEnvSetG = CreateTXCollection(100)
	}

	return GlobalEnvSetG.Contains(vA)
}

// 字符串相关函数 string related

func IsEmptyTrim(strA string) bool {
	return (Trim(strA) == "")
}

// StartsWith 检查字符串strA开始是否是subStrA
func StartsWith(strA string, subStrA string) bool {

	return strings.HasPrefix(strA, subStrA)
}

func StartsWithIgnoreCase(strA string, subStrA string) bool {

	return strings.HasPrefix(strings.ToLower(strA), strings.ToLower(subStrA))
}

func StartsWithUpper(wordA string) bool {
	if len(wordA) < 1 {
		return false
	}

	return (wordA[0] >= 'A') && (wordA[0] <= 'Z')
}

func StartsWithDigit(strA string) bool {
	if len(strA) < 1 {
		return false
	}

	ts := strA[0:1]
	switch ts {
	case "0", "1", "2", "3", "4", "5", "6", "7", "8", "9":
		return true
	default:
		return false

	}
}

func Contains(strA string, subStrA string) bool {
	return strings.Contains(strA, subStrA)
}

func ContainsIgnoreCase(strA string, subStrA string) bool {
	return strings.Contains(strings.ToLower(strA), strings.ToLower(subStrA))
}

func ToLower(strA string) string {
	return strings.ToLower(strA)
}

func ToUpper(strA string) string {
	return strings.ToUpper(strA)
}

// EndsWith 检查字符串strA结尾是否是subStrA
func EndsWith(strA string, subStrA string) bool {

	return strings.HasSuffix(strA, subStrA)
}

// EndsWithIgnoreCase 检查字符串strA结尾是否是subStrA，不区分大小写
func EndsWithIgnoreCase(strA string, subStrA string) bool {

	return strings.HasSuffix(strings.ToLower(strA), strings.ToLower(subStrA))
}

// Trim 仅仅封装了strings.TrimSpace
func Trim(strA string) string {
	return strings.TrimSpace(strA)
}

func TrimCharSet(strA string, charSetA string) string {
	return strings.Trim(strA, charSetA)
}

func InStrings(strA string, argsA ...string) bool {
	for _, arg := range argsA {
		if strA == arg {
			return true
		}
	}

	return false
}

func IsValidEmail(strA string) bool {
	return RegMatch(strA, `[a-zA-Z0-9]+?[a-zA-Z0-9\.\-_]*?@[a-zA-Z0-9]+?(\.[a-zA-Z0-9\.\-_]*)+`)
}

func GetSliceMaxLen(strA string, maxBytesA int) string {
	lenT := len(strA)

	if lenT <= maxBytesA {
		return strA
	}

	return strA[:maxBytesA]
}

func FindFirstDiffIndex(strA string, str2A string) int {
	lent1 := len(strA)
	lent2 := len(str2A)

	lent := lent1

	if lent2 < lent {
		lent = lent2
	}

	i := 0

	for i = 0; i < lent; i++ {
		if strA[i] != str2A[i] {
			return i
		}
	}

	if lent1 == lent2 {
		return -1
	}

	return i

}

func FindSamePrefix(strA, str2A string) string {
	idxT := FindFirstDiffIndex(strA, str2A)

	if idxT < 0 {
		return strA
	}

	if idxT > len(strA) {
		return str2A[:idxT]
	}

	return strA[:idxT]
}

// IsErrorString 判断是否表示出错的字符串
func IsErrorString(errStrA string) bool {
	return StartsWith(errStrA, "TXERROR:")
}

func IsErrStr(errStrA string) bool {
	return StartsWith(errStrA, "TXERROR:")
}

// GetErrorString 获取出错字符串中的出错原因部分
func GetErrorString(errStrA string) string {
	if StartsWith(errStrA, "TXERROR:") {
		return errStrA[8:]
	} else {
		return errStrA
	}
}

// GetErrorStringSafely 获取出错字符串中的出错原因部分，如果不是出错字符串则返回原串
func GetErrorStringSafely(errStrA string) string {
	if StartsWith(errStrA, "TXERROR:") {
		return errStrA[8:]
	} else {
		return errStrA
	}
}

func GetErrStr(errStrA string) string {
	if StartsWith(errStrA, "TXERROR:") {
		return errStrA[8:]
	} else {
		return errStrA
	}
}

// GenerateErrorString 生成一个出错字符串
func GenerateErrorString(errStrA string) string {
	return "TXERROR:" + errStrA
}

func ErrStr(errStrA string) string {
	return "TXERROR:" + errStrA
}

// GenerateErrorStringF 生成一个出错字符串，但可以加上格式，类似Printf
func GenerateErrorStringF(formatA string, argsA ...interface{}) string {
	return fmt.Sprintf("TXERROR:"+formatA, argsA...)
}

func ErrStrF(formatA string, argsA ...interface{}) string {
	return fmt.Sprintf("TXERROR:"+formatA, argsA...)
}

// ErrorStringToError convert errorstring to error, if not, return nil
func ErrorStringToError(strA string) error {
	if IsErrorString(strA) {
		return fmt.Errorf("%v", GetErrorString(strA))
	}

	return nil
}

func ErrStrToErr(strA string) error {
	if IsErrorString(strA) {
		return fmt.Errorf("%v", GetErrorString(strA))
	}

	return nil
}

func ErrToStr(errA error) string {
	return fmt.Sprintf("TXERROR:%v", errA.Error())
}

func ErrToStrF(formatA string, errA error) string {
	return fmt.Sprintf("TXERROR:"+formatA, errA.Error())
}

func Replace(strA, findA, replaceA string) string {
	return strings.Replace(strA, findA, replaceA, -1)
}

func StringReplace(strA string, argsA ...string) string {
	if len(argsA) < 2 {
		return strA
	}

	lenT := len(argsA) / 2

	strT := strA
	for i := 0; i < lenT; i++ {
		strT = strings.Replace(strT, argsA[i*2], argsA[i*2+1], -1)
	}

	return strT
}

func SplitLines(strA string) []string {
	if !strings.Contains(strA, "\n") {
		if strings.Contains(strA, "\r") {
			return strings.Split(strA, "\r")
		}
	}
	strT := Replace(strA, "\r", "")
	return strings.Split(strT, "\n")
}

func SplitLinesRemoveEmpty(strA string) []string {
	if !strings.Contains(strA, "\n") {
		if strings.Contains(strA, "\r") {
			strT := RegReplace(strA, "\\r\\s*\\r", "\r")
			return strings.Split(strT, "\r")
		}
	}

	strT := Replace(strA, "\r", "")
	strT = RegReplace(strT, "\\n\\s*\\n", "\n")
	strT = RegReplace(strT, `^\s*\n`, "")
	strT = RegReplace(strT, `\n\s*$`, "")
	return strings.Split(strT, "\n")
}

func Split(strA string, sepA string) []string {
	return strings.Split(strA, sepA)
}

func SplitN(strA string, sepA string, countA int) []string {
	return strings.SplitN(strA, sepA, countA)
}

func JoinLines(strListA []string) string {
	if strListA == nil {
		return GenerateErrorString("nil list")
	}

	return strings.Join(strListA, "\n")
}

func JoinLinesBySeparator(strListA []string, sepA string) string {
	if strListA == nil {
		return GenerateErrorString("nil list")
	}

	return strings.Join(strListA, sepA)
}

// StartsWithBOM if a UTF-8 string starts with BOM
func StartsWithBOM(strA string) bool {
	bom := []byte{0xEF, 0xBB, 0xBF}

	if StartsWith(strA, string(bom)) {
		return true
	}

	return false

}

// RemoveBOM if a UTF-8 string starts with BOM, remove it
func RemoveBOM(strA string) string {
	bufT := []byte(strA)

	if len(bufT) < 3 {
		return strA
	}

	if bufT[0] == 0xEF && bufT[1] == 0xBB && bufT[2] == 0xBF {
		bufT = bufT[3:]
	}

	return string(bufT)

}

// EnsureValidFileNameX 确保文件名合理并且长度合适
func EnsureValidFileNameX(fileNameA string) string {
	rs := EncodeStringSimple(fileNameA)

	var extT string
	if len(rs) > 180 {
		extT = filepath.Ext(rs)

		var tmpfn string
		if extT == "" {
			tmpfn = rs
		} else {
			tmpfn = rs[:len(rs)-len(extT)]
		}

		if len(extT) > 30 {
			extT = extT[:30]
			extT = RegReplace(extT, `(%[A-F0-9]?)$`, "")
		}

		if len(tmpfn) > 160 {
			tmpfn = tmpfn[:180]
			tmpfn = RegReplace(tmpfn, `(%[A-F0-9]?)$`, "")
		}

		return tmpfn + extT
	}

	tmps := RegReplace(rs, `(%[A-F0-9]?)$`, "")
	if tmps != rs {
		return tmps
	}

	tmps = RegReplace(tmps, `(%[A-F0-9]?)(\.[^\.]*?)$`, "$2")
	return tmps
}

// TXString 相关

type TXString struct {
	string
	Err string
	Obj interface{}
}

func CreateString(strA string, errA string) *TXString {
	strT := &TXString{}
	strT.string = strA
	strT.Err = errA
	return strT
}

func CreateStringSimple(strA string) *TXString {
	return &TXString{string: strA, Err: ""}
}

func CreateStringWithObject(strA string, objA interface{}) *TXString {
	return &TXString{string: strA, Err: "", Obj: objA}
}

func CreateStringEmpty() *TXString {
	return &TXString{string: "", Err: ""}
}

func CreateStringSuccess() *TXString {
	return &TXString{string: "", Err: ""}
}

func CreateStringError(errA string) *TXString {
	return &TXString{string: "", Err: errA}
}

func CreateStringErrorF(formatA string, argsA ...interface{}) *TXString {
	return &TXString{string: "", Err: fmt.Sprintf(formatA, argsA...)}
}

func CreateStringErrorFromTXError(errA string) *TXString {
	if IsErrorString(errA) {
		return &TXString{string: "", Err: GetErrorString(errA)}
	}

	return &TXString{string: errA, Err: ""}
}

func (p *TXString) String() string {
	return p.string
}

func (p *TXString) Length() int {
	return len(p.string)
}

func (p *TXString) CutToLen(lenA int) string {
	p.string = p.string[:lenA]
	return p.string
}

func (p *TXString) Error() string {
	return p.Err
}

func (p *TXString) JSONString() string {
	return ObjectToJSON(p)
}

func (p *TXString) StringEmptyIfError() string {
	if p.IsError() {
		return ""
	}
	return p.string
}

func (p *TXString) InitWithString(strA string) *TXString {
	p.string = strA
	p.Err = ""
	return p
}

func (p *TXString) Set(strA string) *TXString {
	p.string = strA
	p.Err = ""
	return p
}

func (p *TXString) Trim() *TXString {
	p.string = Trim(p.string)
	return p
}

func (p *TXString) SplitLines() []string {
	return SplitLines(p.string)
}

func (p *TXString) IsError() bool {
	return (p.Err != "")
}

func (p *TXString) IsErrStr() bool {
	return IsErrStr(p.string)
}

func (p *TXString) Print() {
	Pl("string: %v, error: %v", p.string, p.Err)
}

func (p *TXString) PrintWithPrefixTime(prefixA string) {
	Pl("[%v] %vstring: %v, error: %v", GetNowTimeStringFormal(), prefixA, p.string, p.Err)
}

func (p *TXString) PrintWithPrefixTimeLast(prefixA string) {
	Pl("%vstring: %v, error: %v, [%v]", prefixA, p.string, p.Err, GetNowTimeStringFormal())
}

func (p *TXString) PrintWithTimeLast() {
	Pl("string: %v, error: %v, [%v]", p.string, p.Err, GetNowTimeStringFormal())
}

func (p *TXString) PrintResultWithTimeLast() {
	if p.IsError() {
		Pl("Error: %v [%v]", p.Err, GetNowTimeStringFormal())
	} else {
		Pl("Success: %v [%v]", p.string, GetNowTimeStringFormal())
	}
}

func (p *TXString) Replace(patternA string, replacementA string) *TXString {
	p.string = Replace(p.string, patternA, replacementA)

	return p
}

func (p *TXString) Contains(patternA string) bool {
	return strings.Contains(p.string, patternA)
}

func (p *TXString) RegReplace(patternA string, replacementA string) *TXString {
	p.string = RegReplace(p.string, patternA, replacementA)

	return p
}

func (p *TXString) RegReplaceX(patternA string, replacementA string) *TXString {
	p.string = RegReplaceX(p.string, patternA, replacementA)

	return p
}

func (p *TXString) RegFindAll(patternA string, groupA int) []string {
	return RegFindAll(p.string, patternA, groupA)
}

func (p *TXString) RegFindFirst(patternA string, groupA int) string {
	return RegFindFirst(p.string, patternA, groupA)
}

func (p *TXString) RegFindFirstX(patternA string, groupA int) string {
	return RegFindFirstX(p.string, patternA, groupA)
}

func (p *TXString) List() []string {
	return SplitLines(p.string)
}

func (p *TXString) ToStringList() []string {
	return SplitLines(p.string)
}

func (p *TXString) ToStringListRemoveEmpty() []string {
	return SplitLinesRemoveEmpty(p.string)
}

func (p *TXString) ErrorString() string {
	return p.Err
}

func (p *TXString) ErrorStringF(formatA string) string {
	return fmt.Sprintf(formatA, p.Err)
}

func (p *TXString) EQ(strA string) bool {
	return (p.string == strA)
}

func (p *TXString) Equals(strA string) bool {
	return (p.string == strA)
}

func (p *TXString) EqualsIgnoreCase(strA string) bool {
	return (strings.ToLower(p.string) == strings.ToLower(strA))
}

func (p *TXString) StartsWith(strA string) bool {
	return StartsWith(p.string, strA)
}

func (p *TXString) EndsWith(strA string) bool {
	return EndsWith(p.string, strA)
}

func (p *TXString) IsEmpty() bool {
	return (p.string == "")
}

func (p *TXString) IsEmptyTrim() bool {
	return (Trim(p.string) == "")
}

func (p *TXString) ContainsInHtmlAttributeString(substrA string) bool {
	tmpStr := p.Trim()
	if tmpStr.IsEmpty() {
		return false
	}

	if tmpStr.EQ(substrA) {
		return true
	} else if tmpStr.StartsWith(substrA + " ") {
		return true
	} else if tmpStr.EndsWith(" " + substrA) {
		return true
	}

	return false
}

func (p *TXString) PlErr(prefixA string) *TXString {
	if p.IsError() {
		Pl(prefixA + p.Err)
	}

	return p
}

func (p *TXString) PlSuccessOrErr(workA string) *TXString {
	if p.IsError() {
		Pl(workA + " failed: " + p.Err)
	} else {
		Pl(workA + " successfully")
	}

	return p
}

func (p *TXString) Save(fileA string) *TXString {
	if p.IsError() {
		return p
	}

	p.Err = SaveStringToFile(p.string, fileA)
	return p
}

type TXStringSlice struct {
	body []string
}

type TXStringArray []string

func (aryM TXStringArray) Contains(strA string) bool {
	if len(aryM) < 1 {
		return false
	}

	for _, v := range aryM {
		if v == strA {
			return true
		}
	}

	return false
}

func (aryM TXStringArray) ContainsIgnoreCase(strA string) bool {
	if len(aryM) < 1 {
		return false
	}

	for _, v := range aryM {
		if strings.ToLower(v) == strings.ToLower(strA) {
			return true
		}
	}

	return false
}

func GenerateErrorStringTX(errStrA string) *TXString {
	return CreateString("", errStrA)
}

func GenerateErrorStringFTX(formatA string, argsA ...interface{}) *TXString {
	return CreateString("", fmt.Sprintf(formatA, argsA...))
}

func LoadStringTX(fileNameA string) *TXString {
	if !IfFileExists(fileNameA) {
		return GenerateErrorStringTX("file not exists")
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return GenerateErrorStringTX(err.Error())
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return GenerateErrorStringTX(err.Error())
	}

	return CreateStringSimple(string(fileContentT))
}

func RegContains(strA, patternA string) bool {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return false
	}

	return !(regexpT.FindStringIndex(strA) == nil)
}

func RegContainsX(strA, patternA string) bool {
	regexpT, errT := regexpx.Compile(patternA)

	if errT != nil {
		return false
	}

	return !(regexpT.FindStringIndex(strA) == nil)
}

func RegFindFirstTX(strA, patternA string, groupA int) *TXString {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return CreateStringError("invalid pattern")
	}

	rT := regexpT.FindStringSubmatch(strA)
	if rT == nil {
		return CreateStringError("no match")
	}

	if groupA < len(rT) {
		return CreateStringSimple(rT[groupA])
	}

	return CreateStringError("no group")
}

func LoadDualLineListFromString(strA string) [][]string {
	rs := SplitLines(strA)

	lenT := len(rs) / 2

	bufT := make([][]string, lenT)

	var bufP []string

	for i := 0; i < lenT; i++ {
		bufP = make([]string, 2)

		bufP[0] = rs[i*2]
		bufP[1] = rs[i*2+1]

		bufT[i] = bufP
	}

	return bufT
}

// 正则表达式相关 regex related

func RegReplace(strA, patternA, replaceA string) string {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return strA
	}

	return regexpT.ReplaceAllString(strA, replaceA)
}

func RegReplaceX(strA, patternA, replaceA string) string {
	regexpT, errT := regexpx.Compile(patternA)

	if errT != nil {
		return strA
	}

	return regexpT.ReplaceAllString(strA, replaceA)
}

func RegFindAll(strA, patternA string, groupA int) []string {
	regexpT, errT := regexp.Compile(patternA)
	if errT != nil {
		return nil
	}

	rT := regexpT.FindAllStringSubmatch(strA, -1)
	if rT == nil {
		return nil
	}

	if groupA < len(rT[0]) {
		rAryT := make([]string, 0, len(rT[0]))
		for i := range rT {
			rAryT = append(rAryT, rT[i][groupA])
		}
		return rAryT
	}

	return nil
}

func RegFindAllX(strA, patternA string, groupA int) []string {
	regexpT, errT := regexpx.Compile(patternA)
	if errT != nil {
		return nil
	}

	rT := regexpT.FindAllStringSubmatch(strA, -1)
	if rT == nil {
		return nil
	}

	if groupA < len(rT[0]) {
		rAryT := make([]string, 0, len(rT[0]))
		for i := range rT {
			rAryT = append(rAryT, rT[i][groupA])
		}
		return rAryT
	}

	return nil
}

func RegFindAllGroups(strA, patternA string) [][]string {
	regexpT, errT := regexp.Compile(patternA)
	if errT != nil {
		return nil
	}

	return regexpT.FindAllStringSubmatch(strA, -1)
}

func RegFindAllGroupsX(strA, patternA string) [][]string {
	regexpT, errT := regexpx.Compile(patternA)
	if errT != nil {
		return nil
	}

	return regexpT.FindAllStringSubmatch(strA, -1)
}

// RegFindFirst returns error string if no match or no matching group
func RegFindFirst(strA, patternA string, groupA int) string {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return GenerateErrorStringF("invalid pattern")
	}

	rT := regexpT.FindStringSubmatch(strA)
	if rT == nil {
		return GenerateErrorString("no match")
	}

	if groupA < len(rT) {
		return rT[groupA]
	}

	return GenerateErrorString("no group")
}

func RegFindFirstX(strA, patternA string, groupA int) string {
	regexpT, errT := regexpx.Compile(patternA)

	if errT != nil {
		return GenerateErrorStringF("invalid pattern")
	}

	rT := regexpT.FindStringSubmatch(strA)
	if rT == nil {
		return GenerateErrorString("no match")
	}

	if groupA < len(rT) {
		return rT[groupA]
	}

	return GenerateErrorString("no group")
}

// RegFindFirstIndex the first match location
func RegFindFirstIndex(strA, patternA string) (int, int) {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return -1, -1
	}

	rT := regexpT.FindStringIndex(strA)
	if rT == nil {
		return -1, -1
	}

	return rT[0], rT[1]
}

func RegFindFirstIndexX(strA, patternA string) (int, int) {
	regexpT, errT := regexpx.Compile(patternA)

	if errT != nil {
		return -1, -1
	}

	rT := regexpT.FindStringIndex(strA)
	if rT == nil {
		return -1, -1
	}

	return rT[0], rT[1]
}

func RegStartsWith(strA, patternA string) bool {
	startT, _ := RegFindFirstIndex(strA, patternA)

	if startT == 0 {
		return true
	}

	return false
}

func RegStartsWithX(strA, patternA string) bool {
	startT, _ := RegFindFirstIndexX(strA, patternA)

	if startT == 0 {
		return true
	}

	return false
}

func RegMatch(strA, patternA string) bool {
	regexpT, errT := regexp.Compile(patternA)

	if errT != nil {
		return false
	}

	tmps := regexpT.FindString(strA)
	if tmps == strA {
		idxt := regexpT.FindStringIndex(strA)

		if idxt != nil {
			return true
		}

		return false
	}

	return false
}

func RegMatchX(strA, patternA string) bool {
	regexpT, errT := regexpx.Compile(patternA)

	if errT != nil {
		return false
	}

	tmps := regexpT.FindString(strA)
	if tmps == strA {
		idxt := regexpT.FindStringIndex(strA)

		if idxt != nil {
			return true
		}

		return false
	}

	return false
}

// 随机数相关 random related

var ifRandomizedG = false

// Randomize 初始化随机数种子
func Randomize() {
	if !ifRandomizedG {
		rand.Seed(time.Now().Unix())
		ifRandomizedG = true
	}
}

// GetRandomIntLessThan 获取[0-maxA)之间的随机数
func GetRandomIntLessThan(maxA int) int {
	Randomize()

	randT := rand.Intn(maxA)

	return randT
}

func GetRandomInt64LessThan(maxA int64) int64 {
	Randomize()

	randT := rand.Int63n(maxA)

	return randT
}

// GetRandomIntInRange 获取[minA-maxA]之间的随机数
func GetRandomIntInRange(minA int, maxA int) int {
	Randomize()

	randT := rand.Intn(maxA+1-minA) + minA

	return randT
}

func GetRandomInt64InRange(minA int64, maxA int64) int64 {
	Randomize()

	randT := rand.Int63n(maxA+1-minA) + minA

	return randT
}

func GenerateRandomString(minCharA, maxCharA int, hasUpperA, hasLowerA, hasDigitA, hasSpecialCharA, hasSpaceA bool, hasInvalidChars bool) string {
	Randomize()

	if minCharA <= 0 {
		return ""
	}

	if maxCharA <= 0 {
		return ""
	}

	if minCharA > maxCharA {
		return ""
	}

	countT := minCharA + rand.Intn(maxCharA+1-minCharA)

	baseT := ""
	if hasUpperA {
		baseT += "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	}

	if hasLowerA {
		baseT += "abcdefghijklmnopqrstuvwxyz"
	}

	if hasDigitA {
		baseT += "0123456789"
	}

	if hasSpecialCharA {
		baseT += "!@#$%^&*-=[]{}."
	}

	if hasSpaceA {
		baseT += " "
	}

	if hasInvalidChars {
		baseT += "/\\:*\"<>|(),+?;"
	}

	rStrT := ""
	var idxT int

	for i := 0; i < countT; i++ {
		idxT = rand.Intn(len(baseT))
		rStrT += baseT[idxT:(idxT + 1)]
	}

	return rStrT
}

// RandomX 是一个线程不安全的随机数产生器
type RandomX struct {
	r uint64
}

func (p *RandomX) Randomize() {
	tmpc := time.Now().UnixNano()

	tmpc = (tmpc & 0x0000FFFF) ^ tmpc

	p.r = uint64(tmpc)
}

func NewRandomGenerator() *RandomX {
	p := &RandomX{r: 0}

	p.Randomize()

	return p
}

func (p *RandomX) Int64() int64 {
	tmpc := p.r

	tmpc ^= tmpc << 13
	tmpc ^= tmpc >> 17
	tmpc ^= tmpc << 5

	if tmpc < 0 {
		tmpc = -tmpc
	}

	p.r = tmpc
	return int64(tmpc)
}

func (p *RandomX) Float64() float64 {
	tmpc := p.Int64N(1000000000)

	tmpf := float64(tmpc) / 1000000000.0

	return tmpf
}

func (p *RandomX) Int64N(maxA int64) int64 {
	tmpc := p.Int64() % maxA
	if tmpc < 0 {
		tmpc = -tmpc
	}

	return tmpc
}

func (p *RandomX) Int() int {
	tmpc := p.Int64()

	return int(tmpc)
}

// ShuffleStringArray 把字符串数组随机化打乱timesA次
func ShuffleStringArray(aryA []string, timesA int) {
	Randomize()

	var x, y int
	lent := len(aryA)
	for i := 0; i < timesA; i++ {
		x = GetRandomIntLessThan(lent)
		y = GetRandomIntLessThan(lent)
		if x == y {
			i--
			continue
		}

		aryA[x], aryA[y] = aryA[y], aryA[x]
	}
}

// GetRandomizeStringArrayCopy 获得一个随机化后的字符串数组
func GetRandomizeStringArrayCopy(aryA []string) []string {
	Randomize()

	lenT := len(aryA)

	aryT := aryA[0:lenT]

	rs := make([]string, lenT)

	var idxT int

	for i := 0; i < lenT; i++ {
		idxT = GetRandomIntLessThan(len(aryT))

		rs[i] = aryT[idxT]

		aryT = DeleteItemInStringArray(aryT, idxT)
	}

	return rs
}

func GetRandomizeSubStringArrayCopy(aryA []string, subCountA int) []string {
	Randomize()

	lenT := len(aryA)

	if subCountA > lenT {
		return nil
	}

	aryT := aryA[0:lenT]

	rs := make([]string, subCountA)

	for i := 0; i < subCountA; i++ {
		idxT := GetRandomIntLessThan(len(aryT))

		rs[i] = aryT[idxT]

		aryT = DeleteItemInStringArray(aryT, idxT)
	}

	return rs
}

// GetRandomizeIntArrayCopy 获得一个随机化顺序后的int数组
func GetRandomizeIntArrayCopy(aryA []int) []int {
	Randomize()

	lenT := len(aryA)

	aryT := aryA[0:lenT]

	rs := make([]int, lenT)

	var idxT int

	for i := 0; i < lenT; i++ {
		idxT = GetRandomIntLessThan((len(aryT)))

		rs[i] = aryT[idxT]

		aryT = DeleteItemInIntArray(aryT, idxT)
	}

	return rs
}

func GetRandomizeInt64ArrayCopy(aryA []int64) []int64 {
	Randomize()

	lenT := len(aryA)

	aryT := aryA[0:lenT]

	rs := make([]int64, lenT)

	var idxT int64

	for i := 0; i < lenT; i++ {
		idxT = GetRandomInt64LessThan((int64)(len(aryT)))

		rs[i] = aryT[idxT]

		aryT = DeleteItemInInt64Array(aryT, idxT)
	}

	return rs
}

func GetRandomSubDualList(listA [][]string, countA int) [][]string {
	if countA > len(listA) {
		countA = len(listA)
	}

	l := make([][]string, countA)

	if countA < 1 {
		return l
	}

	mapt := make(map[int]bool)

	lent := len(listA)

	for i := 0; i < countA; i++ {
		for true {
			idx := GetRandomIntLessThan(lent)
			if !mapt[idx] {
				mapt[idx] = true
				l[i] = listA[idx]
				break
			}
		}
	}

	return l
}

func JoinDualList(listA [][]string, sepItemA, sepInItemA string, withLineNumberA bool) string {
	if listA == nil {
		return ""
	}

	var bufT bytes.Buffer

	for i, v := range listA {
		if i != 0 {
			bufT.WriteString(sepItemA)

		}

		if withLineNumberA {
			bufT.WriteString(Spr("%v. ", i+1))
		}

		bufT.WriteString(v[0])
		bufT.WriteString(sepInItemA)
		bufT.WriteString(v[1])
	}

	return bufT.String()
}

// 时间相关 time related

// GetNowDateString output likes 20150409
func GetNowDateString() string {
	t := time.Now()
	return fmt.Sprintf("%04d%02d%02d", t.Year(), t.Month(), t.Day())
}

// GetNowTimeString GetNowTimeString
// "20060102150405"
func GetNowTimeString() string {
	t := time.Now()
	return fmt.Sprintf("%04d%02d%02d%02d%02d%02d", t.Year(), t.Month(), t.Day(), t.Hour(), t.Minute(), t.Second())
}

// GetNowTimeStringFormat GetNowTimeStringFormat
// "2006-01-02 15:04:05.000"
func GetNowTimeStringFormat(formatA string) string {
	t := time.Now()
	return t.Format(formatA)
}

// GetNowTimeStringFormal get the time string for now as "2020-02-02 08:09:15"
func GetNowTimeStringFormal() string {
	t := time.Now()
	return fmt.Sprintf("%04d-%02d-%02d %02d:%02d:%02d", t.Year(), t.Month(), t.Day(), t.Hour(), t.Minute(), t.Second())
}

func GetNowTimeOnlyStringBeijing() string {
	t := time.Now()
	loc := time.FixedZone("GMT+08:00", 8*3600)
	t = t.In(loc)
	return fmt.Sprintf("%02d%02d%02d", t.Hour(), t.Minute(), t.Second())
}

func GetTimeFromUnixTimeStamp(timeStampA int64) time.Time {
	return time.Unix(timeStampA, 0)
}

func GetTimeFromUnixTimeStampMid(timeStampStrA string) time.Time {
	if len(timeStampStrA) < 13 {
		return time.Time{}
	}

	return time.Unix(StrToInt64WithDefaultValue(timeStampStrA[:10], 0), StrToInt64WithDefaultValue(timeStampStrA[10:], 0))
}

func GetTimeStamp(timeA time.Time) string {
	return Int64ToStr(timeA.Unix())
}

func GetTimeStampMid(timeA time.Time) string {
	return Int64ToStr(timeA.UnixNano())[:13]
}

func GetTimeStampNano(timeA time.Time) string {
	return Int64ToStr(timeA.UnixNano())
}

func NowToFileName() string {
	return StringReplace(time.Now().String(), "-", "_", " ", "_", ":", "_", ".", "_", "+", "_", "=", "_")
}

func GetNowTimeStringHourMinute() string {
	t := time.Now()
	return fmt.Sprintf("%02d:%02d", t.Hour(), t.Minute())
}

func GetNowMinutesInDay() int {
	t := time.Now()

	rs := int(t.Hour())*60 + int(t.Minute())

	return rs
}

func NowToStrUTC(formatA string) string {
	n := time.Now().UTC()
	if formatA == "" {
		return (n.Format(TimeFormat))
	}

	return n.Format(formatA)
}

func GetTimeStringDiffMS(str1A, str2A, formatA string, defaultA int64) int64 {
	formatT := Trim(formatA)
	if formatT == "" {
		formatT = TimeFormat
	}

	t1, err := time.Parse(formatT, str1A)
	if err != nil {
		return defaultA
	}

	t2, err := time.Parse(formatT, str2A)
	if err != nil {
		return defaultA
	}

	diffT := t2.Sub(t1)

	return int64(diffT / 1000000)
}

// return: 1 if str1A > str2A, -1 if str1A < str2A, 0: equal, error if invalid format
func CompareTimeString(str1A, str2A, formatA string) (int, error) {
	formatT := Trim(formatA)
	if formatT == "" {
		formatT = TimeFormat
	}

	t1, err := time.Parse(formatT, str1A)
	if err != nil {
		return 0, Errf("invalid format for time1")
	}

	t2, err := time.Parse(formatT, str2A)
	if err != nil {
		return 0, Errf("invalid format for time2")
	}

	diffT := t2.Sub(t1)

	if diffT > 0 {
		return -1, nil
	} else if diffT < 0 {
		return 1, nil
	}

	return 0, nil
}

func StrToTime(strA string, defaultA time.Time) time.Time {
	t, err := time.Parse(TimeFormat, strA)
	if err != nil {
		return defaultA
	}

	return t
}

// StrToTimeByFormat default "2006-01-02 15:04:05"
func StrToTimeByFormat(strA string, formatA string) (time.Time, error) {

	if formatA == "" {
		formatA = "2006-01-02 15:04:05"
	}

	return time.ParseInLocation(formatA, strA, time.Local)
}

// FormatTime default format "2006-01-02 15:04:05"
func FormatTime(timeA time.Time, formatA string) string {
	if formatA == "" {
		formatA = "2006-01-02 15:04:05"
	}

	return timeA.Format(formatA)
}

// IsYesterday 判断字符串是否是昨天，formatA默认为"20060102"格式
func IsYesterday(dateStrA string, formatA string) bool {
	if formatA == "" {
		formatA = "20060102"
	}

	// dateT, errT := time.Parse(formatA, dateStrA)
	// if errT != nil {
	// 	return false
	// }

	if time.Now().Add(time.Hour*24*time.Duration(-1)).Format(formatA) == dateStrA {
		return true
	}

	return false
}

// 切片、数组相关 slice related and array related

func GetRandomItem(aryA []interface{}) interface{} {
	if aryA == nil {
		return nil
	}

	lenT := len(aryA)

	return aryA[GetRandomIntLessThan(lenT)]
}

func PickRandomItem(aryA []interface{}) interface{} {
	if aryA == nil {
		return nil
	}

	lenT := len(aryA)

	idxT := GetRandomIntLessThan(lenT)

	itemT := aryA[idxT]

	DeleteItemInArray(aryA, idxT)

	return itemT
}

func GetRandomStringItem(aryA []string) string {
	if aryA == nil {
		return ErrStrF("nil input")
	}

	lenT := len(aryA)

	return aryA[GetRandomIntLessThan(lenT)]
}

// DeleteItemInStringArray 删除字符串切片中的某一项
func DeleteItemInStringArray(aryA []string, idxA int) []string {
	rs := make([]string, 0, len(aryA)-1)
	rs = append(rs, aryA[:idxA]...)
	rs = append(rs, aryA[idxA+1:]...)
	return rs
}

// DeleteItemInArray 删除切片中的某一项
func DeleteItemInArray(aryA []interface{}, idxA int) []interface{} {
	rs := make([]interface{}, 0, len(aryA)-1)
	rs = append(rs, aryA[:idxA]...)
	rs = append(rs, aryA[idxA+1:]...)
	return rs
}

// DeleteItemInIntArray 删除字符串切片中的某一项
func DeleteItemInIntArray(aryA []int, idxA int) []int {
	rs := make([]int, 0, len(aryA)-1)
	rs = append(rs, aryA[:idxA]...)
	rs = append(rs, aryA[idxA+1:]...)
	return rs
}

func DeleteItemInInt64Array(aryA []int64, idxA int64) []int64 {
	rs := make([]int64, 0, len(aryA)-1)
	rs = append(rs, aryA[:idxA]...)
	rs = append(rs, aryA[idxA+1:]...)
	return rs
}

func DeleteItemInFloat64Array(aryA []float64, idxA int64) []float64 {
	rs := make([]float64, 0, len(aryA)-1)
	rs = append(rs, aryA[:idxA]...)
	rs = append(rs, aryA[idxA+1:]...)
	return rs
}

func ContainsIn(strA string, subStrsA ...string) bool {
	for _, v := range subStrsA {
		if strings.Contains(strA, v) {
			return true
		}
	}

	return false
}

func ContainsInStringList(strA string, strListA []string) bool {
	if strListA == nil {
		return false
	}

	for _, v := range strListA {
		if strA == v {
			return true
		}
	}

	return false
}

func IndexInStringList(strA string, strListA []string) int {
	if strListA == nil {
		return -1
	}

	for i, v := range strListA {
		if strA == v {
			return i
		}
	}

	return -1
}

func IndexInStringListFromEnd(strA string, strListA []string) int {
	if strListA == nil {
		return -1
	}

	lent := len(strListA)

	for i := lent - 1; i >= 0; i-- {
		if strA == strListA[i] {
			return i
		}
	}

	return -1
}

func GetStringSliceFilled(filledString string, countA int) []string {
	if countA < 0 {
		countA = 0
	}

	bufT := make([]string, countA)

	for i := 0; i < countA; i++ {
		bufT[i] = filledString
	}

	return bufT
}

// Len64 返回int64结果的len
func Len64(aryA []string) int64 {
	return (int64)(len(aryA))
}

func Int64ArrayToFloat64Array(aryA []int64) []float64 {
	if aryA == nil {
		return nil
	}

	lent := len(aryA)
	rs := make([]float64, lent)

	for i := 0; i < lent; i++ {
		rs[i] = float64(aryA[i])

	}

	return rs

}

func ByteSliceToStringDec(bufA []byte, sepA string) string {
	if bufA == nil {
		return ""
	}

	var outBufT strings.Builder

	lenT := len(bufA)

	for i := 0; i < lenT; i++ {
		if i != 0 {
			outBufT.WriteString(sepA)
		}

		outBufT.WriteString(fmt.Sprintf("%d", bufA[i]))
	}

	return outBufT.String()
}

// 映射相关 map related

// GetValueOfMSS get the value for key in map[string]string
// returns default value if not ok
func GetValueOfMSS(mapA map[string]string, keyA string, defaultA string) string {
	v, ok := mapA[keyA]

	if ok {
		return v
	}

	return defaultA
}

// 系统相关函数 system related

// GetOSArgs return os.Args
func GetOSArgs() []string {
	return os.Args
}

func GetOSArgsShort() []string {
	return os.Args[1:]
}

// EnsureBasePath make sure a base path for application is exists, otherwise create it
// first look for c:\nameA(Windows) or /nameA(Mac&Linux), then the application path
// if nameA contains ".", "/", "\\", will use it as basepath instead
func EnsureBasePath(nameA string) (string, error) {
	var basePathT string

	if ContainsIn(nameA, ".", "/", "\\") {
		baseT, errT := filepath.Abs(nameA)
		if errT != nil {
			return "", errT
		}

		basePathT = baseT
	} else {
		if strings.HasPrefix(runtime.GOOS, "win") {
			basePathT = "c:\\" + nameA
		} else {
			basePathT = "/" + nameA
		}

		errT := EnsureMakeDirsE(basePathT)

		if (errT != nil) || (!IfFileExists(basePathT)) {
			basePathT = GetApplicationPath()
		}

	}

	// filePathT := filepath.Join(basePathT, "basePathT.txt")

	// errT = SaveStringToFileE("test", filePathT)

	// if (errT != nil) || (!IfFileExists(filePathT)) {
	// 	return "", Errf("init base path failed")
	// }

	// errT = RemoveFile(filePathT)

	// if (errT != nil) || (IfFileExists(filePathT)) {
	// 	return "", Errf("init base path failed: failed to remove tmp file")
	// }

	return basePathT, nil
}

func CreateTempFile(dirA string, patternA string) (string, error) {
	content := []byte("")
	tmpfile, err := ioutil.TempFile(dirA, patternA)
	if err != nil {
		return "", err
	}

	defer tmpfile.Close()

	rs := tmpfile.Name()

	// defer os.Remove(tmpfile.Name()) // clean up

	if _, err := tmpfile.Write(content); err != nil {
		return rs, err
	}

	if err := tmpfile.Close(); err != nil {
		return rs, err
	}

	return rs, nil
}

//
func CopyFile(src, dst string, forceA bool, bufferSizeA int) error {

	srcFileStat, err := os.Stat(src)
	if err != nil {
		return err
	}

	mode := srcFileStat.Mode()

	if !mode.IsRegular() {
		return fmt.Errorf("%s is not a regular file", src)
	}

	if mode.IsDir() {
		return fmt.Errorf("%s is a folder", src)
	}

	source, err := os.Open(src)
	if err != nil {
		return err
	}

	defer source.Close()

	if !forceA {
		_, err = os.Stat(dst)
		if err != nil {
			return fmt.Errorf("file %s already exists", dst)
		}
	}

	destination, err := os.Create(dst)
	if err != nil {
		return err
	}

	defer destination.Close()

	if bufferSizeA <= 0 {
		bufferSizeA = 1000000
	}

	buf := make([]byte, bufferSizeA)
	for {
		n, err := source.Read(buf)

		if err != nil && err != io.EOF {
			return err
		}

		if n == 0 {
			break
		}

		if _, err := destination.Write(buf[:n]); err != nil {
			return err
		}
	}

	return err
}

// GetCurrentThreadID get goroutineid
func GetCurrentThreadID() string {
	var buf [64]byte

	n := runtime.Stack(buf[:], false)

	idField := strings.Fields(strings.TrimPrefix(string(buf[:n]), "goroutine "))[0]

	id, errT := strconv.Atoi(idField)
	if errT != nil {
		return GenerateErrorStringF("failed to get goroutine id: %v", errT)
	}

	return IntToStr(id)
}

// Exit usage: Exit() or Exit(number)
func Exit(c ...int) {
	if c == nil || len(c) < 1 {
		os.Exit(0)
	}

	os.Exit(c[0])
}

// RunWinFileWithSystemDefault run a program or open a file with default program in Windows
func RunWinFileWithSystemDefault(fileA string) string {
	cmd := exec.Command("cmd", "/C", "start", "", fileA)
	err := cmd.Start()
	if err != nil {
		return err.Error()
	}
	return ""
}

// SystemCmd run system command, such as "cmd /c dir", "cmd /k copy a.txt b.txt".
func SystemCmd(cmdA string, argsA ...string) string {
	var out bytes.Buffer

	cmd := exec.Command(cmdA, argsA...)

	cmd.Stdout = &out
	errT := cmd.Run()
	if errT != nil {
		return GenerateErrorStringF("failed: %v", errT)
	}

	return out.String()
}

// NewSSHClient create SSH client with fewer settings
func NewSSHClient(hostA string, portA int, userA string, passA string) (*goph.Client, error) {
	authT := goph.Password(passA)

	clientT := &goph.Client{
		Addr: hostA,
		Port: portA,
		User: userA,
		Auth: authT,
	}

	errT := goph.Conn(clientT, &ssh.ClientConfig{
		User:    clientT.User,
		Auth:    clientT.Auth,
		Timeout: 20 * time.Second,
		HostKeyCallback: func(host string, remote net.Addr, key ssh.PublicKey) error {
			return nil
			// hostFound, err := goph.CheckKnownHost(host, remote, key, "")

			// if hostFound && err != nil {
			// 	return err
			// }

			// if hostFound && err == nil {
			// 	return nil
			// }

			// return goph.AddKnownHost(host, remote, key, "")
		},
	})

	// clientT, errT := goph.NewConn(userA, hostA, authT, func(host string, remote net.Addr, key ssh.PublicKey) error {

	// 	hostFound, err := goph.CheckKnownHost(host, remote, key, "")

	// 	if hostFound && err != nil {
	// 		return err
	// 	}

	// 	if hostFound && err == nil {
	// 		return nil
	// 	}

	// 	return goph.AddKnownHost(host, remote, key, "")
	// })

	return clientT, errT
}

// Prf 仅仅是封装了fmt.Printf函数，但会返回format字符串
func Prf(formatA string, argsA ...interface{}) string {
	fmt.Printf(formatA, argsA...)

	return formatA
}

// Prl 仅仅封装了fmt.Println函数
func Prl(a ...interface{}) {
	fmt.Println(a...)
}

// Pln 仅仅封装了fmt.Println函数
func Pln(a ...interface{}) {
	fmt.Println(a...)
}

// Printf 仅仅封装了fmt.Printf函数，与其完全一致
func Printf(format string, a ...interface{}) {
	fmt.Printf(format, a...)
}

// Printfln 仅仅封装了fmt.Printf函数，但结尾会多输出一个换行符
func Printfln(format string, a ...interface{}) {
	fmt.Printf(format+"\n", a...)
}

// Spr 仅仅是封装了fmt.Sprintf函数
func Spr(formatA string, argsA ...interface{}) string {
	return fmt.Sprintf(formatA, argsA...)
}

// Pr 即fmt.Print
func Pr(argsA ...interface{}) {
	fmt.Print(argsA...)
}

// Pl 类似Pr，但结尾会加有一个回车
func Pl(formatA string, argsA ...interface{}) {
	fmt.Printf(formatA+"\n", argsA...)
}

// PlNow 类似Pl，但前面会加有当前时间标记
func PlNow(formatA string, argsA ...interface{}) {
	fmt.Printf(fmt.Sprintf("[%v] ", time.Now().Format(TimeFormatCompact2))+formatA+"\n", argsA...)
}

// PlVerbose 类似Pl，但仅在verboseA为true时才输出
func PlVerbose(verboseA bool, formatA string, argsA ...interface{}) {
	if verboseA {
		fmt.Printf(formatA+"\n", argsA...)
	}
}

// Fpl 类似Pl，但向流中写入(Fprintf)
func Fpl(wA io.Writer, formatA string, argsA ...interface{}) {
	fmt.Fprintf(wA, formatA+"\n", argsA...)
}

// Fpr 类似Pr，但向流中写入(Fprintf)
func Fpr(wA io.Writer, formatA string, argsA ...interface{}) {
	fmt.Fprintf(wA, formatA, argsA...)
}

func PlvWithError(vA interface{}, errStrA string) {
	if errStrA == "" {
		fmt.Printf("%v\n", vA)
	} else {
		fmt.Printf("Error: %v\n", vA)
	}
}

func PlAndExit(formatA string, argsA ...interface{}) {
	fmt.Printf(formatA+"\n", argsA...)
	os.Exit(0)
}

// PrlErrSimple 输出错误信息，结尾加一个回车
func PlErrSimple(formatA string, argsA ...interface{}) {
	fmt.Printf("Error: "+formatA+"\n", argsA...)
}

func PlErrSimpleAndExit(formatA string, argsA ...interface{}) {
	fmt.Printf("Error: "+formatA+"\n", argsA...)
	os.Exit(0)
}

func PlErrAndExit(errA error) {
	fmt.Printf("Error: " + errA.Error() + "\n")
	os.Exit(0)
}

func PlTXErr(strA string) {
	fmt.Printf("Error: " + GetErrorString(strA) + "\n")
}

func PlSimpleErrorString(strA string) {
	fmt.Printf("Error: " + strA + "\n")
}

func PlErr(errA error) {
	if errA == nil {
		return
	}

	Pl("Error: %v", errA.Error())
}

func PlErrString(strA string) {
	if !IsErrorString(strA) {
		return
	}

	Pl("Error: %v", GetErrorString(strA))
}

func PlErrWithPrefix(prefixA string, errA error) {
	if errA == nil {
		return
	}

	Pl("%v%v", prefixA, errA.Error())
}

// Plv output one variable
func Plv(argsA ...interface{}) {
	fmt.Printf("%#v\n", argsA...)
}

func Plvx(argsA interface{}) {
	fmt.Printf("[TYPE] %T [VALUE] %v [ITYPE] %#v\n", argsA, argsA, argsA)
}

// Plvs output several variables, seperated by sepA
func Plvs(sepA string, argsA ...interface{}) {
	lenT := len(argsA)

	strListA := GetStringSliceFilled("%#v", lenT)

	formatT := strings.Join(strListA, sepA)

	fmt.Printf(formatT+"\n", argsA...)
}

// Plvsr output several variables, seperated by \n (new line character)
func Plvsr(argsA ...interface{}) {
	Plvs("\n", argsA...)
}

// Errf wrap fmt.Errorf function
func Errf(formatA string, argsA ...interface{}) error {
	return fmt.Errorf(formatA, argsA...)
}

func FatalErr(prefixA string, errA error) {
	Pl("%v%v", prefixA, errA.Error())

	os.Exit(1)
}

func FatalErrf(formatA string, errA error) {
	Pl(formatA, errA.Error())

	os.Exit(1)
}

func Fatalf(formatA string, argsA ...interface{}) {
	Pl(formatA, argsA...)

	os.Exit(1)
}

func CheckErr(prefixA string, errA error) {
	if errA == nil {
		return
	}

	Pl("%v%v", prefixA, errA.Error())

	os.Exit(1)
}

func CheckErrf(formatA string, argsA ...interface{}) {
	var errT error = nil

	if argsA == nil {
		return
	}

	for _, v := range argsA {
		tmpV, ok := v.(error)
		if !ok {
			continue
		}

		errT = tmpV
	}

	if errT == nil {
		return
	}

	Pl(formatA, argsA...)

	os.Exit(1)
}

func CheckErrStrf(formatA string, errStrA string, argsA ...interface{}) {
	if !IsErrStr(errStrA) {
		return
	}

	Pl(formatA, append([]interface{}{GetErrStr(errStrA)}, argsA...)...)

	os.Exit(1)
}

func CheckErrCompact(errA error) {
	if errA == nil {
		return
	}

	Prl(errA.Error())

	os.Exit(1)
}

// GetEnv same as os.Getenv
func GetEnv(keyA string) string {
	return os.Getenv(keyA)
}

// JoinPath same as filepath.Join
func JoinPath(elemA ...string) string {
	return filepath.Join(elemA...)
}

// GetUserInput 获取键盘输入，不太可靠
func GetUserInput(promptA string) string {
	if promptA != "" {
		fmt.Print(promptA)
	}

	var textT string
	_, errT := fmt.Scanln(&textT)
	if errT != nil {
		return GenerateErrorString(errT.Error())
	}

	return textT
}

// GetInputf like GetInput, but allows using printf for prompt string
func GetInputf(formatA string, aA ...interface{}) string {
	fmt.Printf(formatA, aA...)

	// var stdinBufferedReaderT *bufio.Reader
	var stdinBufferedScannerT *bufio.Scanner

	stdinBufferedScannerT = bufio.NewScanner(os.Stdin)

	if stdinBufferedScannerT.Scan() {
		rStrT := stdinBufferedScannerT.Text()

		errT := stdinBufferedScannerT.Err()
		if errT != nil {
			if errT == io.EOF {
				return GenerateErrorStringF("EOF", rStrT)
			}

			return GenerateErrorStringF(errT.Error())
		}

		return rStrT
	}

	errT := stdinBufferedScannerT.Err()
	if errT != nil {
		if errT == io.EOF {
			return GenerateErrorStringF("EOF", stdinBufferedScanner.Text())
		}

		return GenerateErrorStringF(errT.Error())
	}

	return GenerateErrorStringF("EOF")
}

var stdinBufferedReader *bufio.Reader
var stdinBufferedScanner *bufio.Scanner

// GetInputBufferedScan 获取键盘输入
func GetInputBufferedScan() string {
	if stdinBufferedScanner == nil {
		stdinBufferedScanner = bufio.NewScanner(os.Stdin)
	}

	if stdinBufferedScanner.Scan() {
		rStrT := stdinBufferedScanner.Text()

		errT := stdinBufferedScanner.Err()
		if errT != nil {
			if errT == io.EOF {
				return GenerateErrorStringF("EOF", rStrT)
			}

			return GenerateErrorStringF(errT.Error())
		}

		return rStrT
	}

	errT := stdinBufferedScanner.Err()
	if errT != nil {
		if errT == io.EOF {
			return GenerateErrorStringF("EOF", stdinBufferedScanner.Text())
		}

		return GenerateErrorStringF(errT.Error())
	}

	return GenerateErrorStringF("EOF")
}

func GetInputPasswordf(formatA string, aA ...interface{}) string {
	fmt.Printf(formatA, aA...)

	bytePassword, err := terminal.ReadPassword(int(syscall.Stdin))
	if err != nil {
		return ErrStrF("failed to get password: %v", err)
	}

	return string(bytePassword)
}

func Sleep(secA float64) {
	time.Sleep(time.Duration(secA) * time.Second)
}

func SleepSeconds(secA int) {
	time.Sleep(time.Duration(secA) * time.Second)
}

func SleepMilliSeconds(msA int) {
	time.Sleep(time.Duration(msA) * time.Millisecond)
}

func GetRuntimeStack() string {
	return string(debug.Stack())
}

func GetOSName() string {
	return runtime.GOOS
}

func GetCurrentDir() string {
	strT, errT := os.Getwd()
	if errT != nil {
		strT, errT = filepath.Abs(".")
		if errT != nil {
			return "."
		}
	}

	return strT
}

func GetApplicationPath() string {
	file, _ := exec.LookPath(os.Args[0])
	pathT, _ := filepath.Abs(file)

	dirT, _ := filepath.Split(pathT)

	return dirT
}

func EnsureMakeDirs(pathA string) string {
	if !IfFileExists(pathA) {
		os.MkdirAll(pathA, 0777)
		return ""
	} else {
		if IsDirectory(pathA) {
			return ""
		} else {
			return GenerateErrorString("a file with same name exists")
		}
	}
}

func EnsureMakeDirsE(pathA string) error {
	if !IfFileExists(pathA) {
		os.MkdirAll(pathA, 0777)

		if !IfFileExists(pathA) {
			return fmt.Errorf("failed to make directory")
		}
		return nil
	} else {
		if IsDirectory(pathA) {
			return nil
		} else {
			return fmt.Errorf("a file with same name exists")
		}
	}
}

// func GetCurrentThreadID() int {
// 	var user32 *syscall.DLL
// 	var GetCurrentThreadId *syscall.Proc
// 	var err error

// 	user32, err = syscall.LoadDLL("Kernel32.dll")
// 	if err != nil {
// 		fmt.Printf("syscall.LoadDLL fail: %v\n", err.Error())
// 		return 0
// 	}
// 	GetCurrentThreadId, err = user32.FindProc("GetCurrentThreadId")
// 	if err != nil {
// 		fmt.Printf("user32.FindProc fail: %v\n", err.Error())
// 		return 0
// 	}

// 	var pid uintptr
// 	pid, _, err = GetCurrentThreadId.Call()

// 	return int(pid)
// }

// 命令行分析

// AnalyzeCommandLineParamter 分解命令行参数，注意如果要带双引号，需要从开始到结束都括上，例如save "-fileName=abc.txt"，而不是save -fileName="abc.txt"
func AnalyzeCommandLineParamter(cmdLineA string) []string {
	return regexp.MustCompile("( |\\\".*?\\\"|'.*?')").Split(cmdLineA, -1)
}

// GetParameterByIndexWithDefaultValue 按顺序序号获取命令行参数，其中0代表第一个参数，也就是软件名称或者命令名称，1开始才是第一个参数，注意参数不包括开关，即类似-verbose=true这样的
func GetParameterByIndexWithDefaultValue(argsA []string, idxA int, defaultA string) string {
	if idxA == -1 {
		idxA = 1
	}

	if (idxA >= len(argsA)) || (idxA < 0) {
		return defaultA
	}

	var cnt int
	for _, argT := range argsA {
		if StartsWith(argT, "-") {
			continue
		}

		if cnt == idxA {
			if StartsWith(argT, "\"") && EndsWith(argT, "\"") {
				return argT[1 : len(argT)-1]
			}

			return argT
		}

		cnt++

	}

	return defaultA
}

func GetParameter(argsA []string, idxA int) string {
	return GetParameterByIndexWithDefaultValue(argsA, idxA, ErrStrF("failed"))
}

// GetAllParameters 获取命令行参数中所有非开关参数
func GetAllParameters(argsA []string) []string {
	aryT := make([]string, 0, len(argsA))

	for _, argT := range argsA {
		if StartsWith(argT, "-") {
			continue
		}

		aryT = append(aryT, argT)
	}

	return aryT
}

func GetAllOSParameters() []string {
	return GetAllParameters(os.Args)
}

// GetAllSwitches 获取命令行参数中所有开关参数
func GetAllSwitches(argsA []string) []string {
	aryT := make([]string, 0, len(argsA))

	for _, argT := range argsA {
		if !StartsWith(argT, "-") {
			continue
		}

		aryT = append(aryT, argT)
	}

	return aryT
}

// ParseCommandLine 分析命令行字符串，类似os.Args的获取过程
func ParseCommandLine(commandA string) ([]string, error) {
	var args []string

	state := "start"
	current := ""
	quote := "\""
	escapeNext := false

	command := []rune(commandA)

	for i := 0; i < len(command); i++ {
		c := command[i]

		if escapeNext {
			current += string(c)
			escapeNext = false
			continue
		}

		if c == '\\' {
			escapeNext = true
			continue
		}

		if state == "quotes" {
			if string(c) != quote {
				current += string(c)
			} else {
				args = append(args, current)
				current = ""
				state = "start"
			}
			continue
		}

		if c == '"' || c == '\'' || c == '`' {
			state = "quotes"
			quote = string(c)
			continue
		}

		if state == "arg" {
			if c == ' ' || c == '\t' {
				args = append(args, current)
				current = ""
				state = "start"
			} else {
				current += string(c)
			}
			// Pl("state: %v, current: %v, args: %v", state, current, args)
			continue
		}

		if c != ' ' && c != '\t' {
			state = "arg"
			current += string(c)
		}
	}

	if state == "quotes" {
		return []string{}, fmt.Errorf("Unclosed quote in command line: %v", command)
	}

	if current != "" {
		args = append(args, current)
	}

	return args, nil
}

// GetSwitchWithDefaultValue 获取命令行参数中的开关，用法：tmps := tk.GetSwitchWithDefaultValue(args, "-verbose=", "false")
func GetSwitchWithDefaultValue(argsA []string, switchStrA string, defaultA string) string {
	if argsA == nil {
		return defaultA
	}

	if len(argsA) < 1 {
		return defaultA
	}

	tmpStrT := ""
	for _, argT := range argsA {
		if StartsWith(argT, switchStrA) {
			tmpStrT = argT[len(switchStrA):]
			if StartsWith(tmpStrT, "\"") && EndsWith(tmpStrT, "\"") {
				return tmpStrT[1 : len(tmpStrT)-1]
			}

			return tmpStrT
		}

	}

	return defaultA

}

func GetSwitch(argsA []string, switchStrA string, defaultA ...string) string {

	ifDefaultT := true
	var defaultT string

	if defaultA == nil || len(defaultA) < 1 {
		ifDefaultT = false
	}

	if ifDefaultT {
		defaultT = defaultA[0]
	}

	if argsA == nil {
		if ifDefaultT {
			return defaultT
		}
		return ErrStr("nil input")
	}

	if len(argsA) < 1 {
		if ifDefaultT {
			return defaultT
		}
		return ErrStr("not exists")
	}

	tmpStrT := ""
	for _, argT := range argsA {
		if StartsWith(argT, switchStrA) {
			tmpStrT = argT[len(switchStrA):]
			if StartsWith(tmpStrT, "\"") && EndsWith(tmpStrT, "\"") {
				return tmpStrT[1 : len(tmpStrT)-1]
			}

			return tmpStrT
		}

	}

	if ifDefaultT {
		return defaultT
	}
	return ErrStr("not exists")
}

func GetSwitchI(argsA []interface{}, switchStrA string, defaultA string) string {
	if argsA == nil {
		return defaultA
	}

	if len(argsA) < 1 {
		return defaultA
	}

	tmpStrT := ""
	for _, argT := range argsA {
		if StartsWith(argT.(string), switchStrA) {
			tmpStrT = argT.(string)[len(switchStrA):]
			if StartsWith(tmpStrT, "\"") && EndsWith(tmpStrT, "\"") {
				return tmpStrT[1 : len(tmpStrT)-1]
			}

			return tmpStrT
		}

	}

	return defaultA

}

// GetSwitchWithDefaultIntValue 与GetSwitchWithDefaultValue类似，返回一个整数
func GetSwitchWithDefaultIntValue(argsA []string, switchStrA string, defaultA int) int {
	tmpStrT := GetSwitchWithDefaultValue(argsA, switchStrA, string(defaultA))

	return StrToIntWithDefaultValue(tmpStrT, defaultA)
}

func GetSwitchWithDefaultInt64Value(argsA []string, switchStrA string, defaultA int64) int64 {
	tmpStrT := GetSwitchWithDefaultValue(argsA, switchStrA, string(defaultA))

	return StrToInt64WithDefaultValue(tmpStrT, defaultA)
}

// IfSwitchExists 判断命令行参数中是否存在开关，用法：flag := IfSwitchExists(args, "-restart")
func IfSwitchExists(argsA []string, switchStrA string) bool {
	if argsA == nil {
		return false
	}

	if len(argsA) < 1 {
		return false
	}

	for _, argT := range argsA {
		if StartsWith(argT, switchStrA) {
			return true
		}

	}

	return false
}

// IfSwitchExistsWhole 判断命令行参数中是否存在开关（完整的，），用法：flag := IfSwitchExistsWhole(args, "-restart")
func IfSwitchExistsWhole(argsA []string, switchStrA string) bool {
	if argsA == nil {
		return false
	}

	if len(argsA) < 1 {
		return false
	}

	for _, argT := range argsA {
		if argT == switchStrA {
			return true
		}

	}

	return false
}

func IfSwitchExistsWholeI(argsA []interface{}, switchStrA string) bool {
	if argsA == nil {
		return false
	}

	if len(argsA) < 1 {
		return false
	}

	for _, argT := range argsA {
		if argT.(string) == switchStrA {
			return true
		}

	}

	return false
}

// 各种转换 conversion related

func StrToBool(strA string) bool {
	lowerStr := strings.ToLower(strA)
	if lowerStr == "yes" || lowerStr == "true" {
		return true
	}

	if lowerStr == "no" || lowerStr == "false" {
		return false
	}

	return false
}

func ByteToHex(byteA byte) string {
	return Spr("%X", byteA)
}

// IntToStr 整形转字符串
func IntToStr(intA int) string {
	return strconv.Itoa(intA)
}

func Int64ToStr(intA int64) string {
	return strconv.FormatInt(intA, 10)
}

func ToStr(v interface{}) string {
	return fmt.Sprintf("%v", v)
}

func ToFloat(v interface{}, defaultA ...float64) (result float64) {
	var defaultT float64

	if defaultA == nil || len(defaultA) < 1 {
		defaultT = 0
	} else {
		defaultT = defaultA[0]
	}

	defer func() {
		r := recover()

		if r != nil {
			result = defaultT
			return
		}
	}()

	switch v.(type) {
	case int:
		result = float64(v.(int))
		return
	case int8:
		result = float64(v.(int8))
		return
	case int16:
		result = float64(v.(int16))
		return
	case int32:
		result = float64(v.(int32))
		return
	case int64:
		result = float64(v.(int64))
		return
	case float64:
		result = v.(float64)
		return
	case float32:
		result = float64(v.(float32))
		return
	case string:
		nT, errT := strconv.ParseFloat(v.(string), 64)
		if errT != nil {
			result = defaultT
			return
		}

		result = nT
		return
	default:
		nT, errT := strconv.ParseFloat(fmt.Sprintf("%v", v), 64)
		if errT != nil {
			result = defaultT
			return
		}

		result = nT
		return
	}
}

func ToInt(v interface{}, defaultA ...int) (result int) {
	var defaultT int

	if defaultA == nil || len(defaultA) < 1 {
		defaultT = 0
	} else {
		defaultT = defaultA[0]
	}

	defer func() {
		r := recover()

		if r != nil {
			result = defaultT
			return
		}
	}()

	switch v.(type) {
	case int:
		result = v.(int)
		return
	case int8:
		result = int(v.(int8))
		return
	case int16:
		result = int(v.(int16))
		return
	case int32:
		result = int(v.(int32))
		return
	case int64:
		result = int(v.(int64))
		return
	case float64:
		result = int(v.(float64))
		return
	case float32:
		result = int(v.(float32))
		return
	case string:
		nT, errT := strconv.ParseInt(v.(string), 10, 0)
		if errT != nil {
			result = defaultT
			return
		}

		result = int(nT)
		return
	default:
		nT, errT := strconv.ParseInt(fmt.Sprintf("%v", v), 10, 0)
		if errT != nil {
			result = defaultT
			return
		}

		result = int(nT)
		return
	}
}

// StrToIntWithDefaultValue 字符串转整数，如果有问题则返回默认数值
func StrToIntWithDefaultValue(strA string, defaultA ...int) int {
	defaultT := -1

	if (defaultA != nil) && (len(defaultA) > 0) {
		defaultT = defaultA[0]
	}

	nT, errT := strconv.ParseInt(strA, 10, 0)
	if errT != nil {
		return defaultT
	}

	return int(nT)
}

// StrToInt 字符串转整数
func StrToInt(strA string, defaultA ...int) int {
	defaultT := -1

	if (defaultA != nil) && (len(defaultA) > 0) {
		defaultT = defaultA[0]
	}

	nT, errT := strconv.ParseInt(strA, 10, 0)
	if errT != nil {
		return defaultT
	}

	return int(nT)
}

// StrToIntE 字符串转整数
func StrToIntE(strA string) (int, error) {
	nT, errT := strconv.ParseInt(strA, 10, 0)

	return int(nT), errT
}

func ToIntI(valueA interface{}, defaultA int) int {
	nT, errT := strconv.ParseInt(fmt.Sprintf("%d", valueA), 10, 0)
	if errT != nil {
		return defaultA
	}

	return int(nT)
}

func StrToInt64(strA string, defaultA ...int64) int64 {
	var defaultT int64 = -1

	if (defaultA != nil) && (len(defaultA) > 0) {
		defaultT = defaultA[0]
	}

	nT, errT := strconv.ParseInt(strA, 10, 0)
	if errT != nil {
		return defaultT
	}

	return nT
}

func StrToInt64WithDefaultValue(strA string, defaultA int64) int64 {
	nT, errT := strconv.ParseInt(strA, 10, 64)
	if errT != nil {
		return defaultA
	}

	return nT
}

func StrToIntPositive(strA string) int {
	nT, errT := strconv.ParseInt(strA, 10, 0)
	if errT != nil {
		return -1
	}

	return int(nT)
}

func StrToFloat64WithDefaultValue(strA string, defaultA float64) float64 {
	nT, errT := strconv.ParseFloat(strA, 64)
	if errT != nil {
		return defaultA
	}

	return nT
}

func StrToFloat64(strA string, defaultA ...float64) float64 {
	var defaultT float64 = -1

	if (defaultA != nil) && (len(defaultA) > 0) {
		defaultT = defaultA[0]
	}

	nT, errT := strconv.ParseFloat(strA, 64)

	if errT != nil {
		return defaultT
	}

	return nT
}

func StrToFloat64E(strA string) (float64, error) {
	nT, errT := strconv.ParseFloat(strA, 64)

	return nT, errT
}

func Float64ToStr(floatA float64) string {
	return fmt.Sprintf("%f", floatA)
}

func StrToTimeCompact(strA string, defaultA time.Time) time.Time {
	t, err := time.Parse(TimeFormatCompact, strA)
	if err != nil {
		return defaultA
	}

	return t
}

func StrToTimeCompactNoError(strA string) time.Time {
	t, _ := time.Parse(TimeFormatCompact, strA)

	return t
}

func FormatStringSliceSlice(sliceA [][]string, sepA string, lineSepA string) string {
	var bufT strings.Builder

	for i, v := range sliceA {
		if i != 0 {
			bufT.WriteString(lineSepA)
		}

		for ii, vv := range v {
			if ii != 0 {
				bufT.WriteString(sepA)
			}

			bufT.WriteString(vv)
		}
	}

	return bufT.String()
}

// IntToKMGT convert a number to "3.21K", "1.2G", etc, formatA like "%.2f"
// if sizeA < 1024, formatA is ignored
func IntToKMGT(sizeA int, formatA string) string {
	if formatA == "" {
		formatA = "%.2f"
	}

	if sizeA >= 1099511627776 {
		return fmt.Sprintf(formatA+"T", float64(sizeA)/1099511627776)
	} else if sizeA >= 1073741824 {
		return fmt.Sprintf(formatA+"G", float64(sizeA)/1073741824)
	} else if sizeA >= 1048576 {
		return fmt.Sprintf(formatA+"M", float64(sizeA)/1048576)
	} else if sizeA >= 1024 {
		return fmt.Sprintf(formatA+"K", float64(sizeA)/1024)
	} else {
		return fmt.Sprintf("%dB", sizeA)
	}
}

// IntToWYZ convert a number to "3.21万", "1.2亿", etc, formatA like "%.2f"
// if sizeA < 1024, formatA is ignored
func IntToWYZ(sizeA int, formatA string) string {
	if formatA == "" {
		formatA = "%.2f"
	}

	if sizeA >= 1000000000000 {
		return fmt.Sprintf(formatA+"兆", float64(sizeA)/1000000000000)
	} else if sizeA >= 100000000 {
		return fmt.Sprintf(formatA+"亿", float64(sizeA)/100000000)
	} else if sizeA >= 10000 {
		return fmt.Sprintf(formatA+"万", float64(sizeA)/10000)
	} else {
		return fmt.Sprintf("%d", sizeA)
	}
}

// 日志相关

func SetLogFile(fileNameA string) {
	logFileG = fileNameA
}

func LogWithTime(formatA string, argsA ...interface{}) {
	if EndsWith(formatA, "\n") {
		AppendStringToFile(fmt.Sprintf(fmt.Sprintf("[%v] ", time.Now())+formatA, argsA...), logFileG)
	} else {
		AppendStringToFile(fmt.Sprintf(fmt.Sprintf("[%v] ", time.Now())+formatA+"\n", argsA...), logFileG)
	}
}

func LogWithTimeCompact(formatA string, argsA ...interface{}) {
	if EndsWith(formatA, "\n") {
		AppendStringToFile(fmt.Sprintf(fmt.Sprintf("[%v] ", time.Now().Format(TimeFormatCompact2))+formatA, argsA...), logFileG)
	} else {
		AppendStringToFile(fmt.Sprintf(fmt.Sprintf("[%v] ", time.Now().Format(TimeFormatCompact2))+formatA+"\n", argsA...), logFileG)
	}
}

// 文件操作相关函数 file related

// IfFileExists 判断文件是否存在
func IfFileExists(fileNameA string) bool {
	_, err := os.Stat(fileNameA)
	return err == nil || os.IsExist(err)
}

// IsFile if is file
func IsFile(fileNameA string) bool {
	f, errT := os.Open(fileNameA)
	if errT != nil {
		return false
	}
	defer f.Close()

	fi, err := f.Stat()
	if err != nil {
		return false
	}

	if mode := fi.Mode(); mode.IsRegular() {
		return true
	}

	return false
}

// IsDirectory if is directory
func IsDirectory(dirNameA string) bool {
	f, err := os.Open(dirNameA)
	if err != nil {
		return false
	}
	defer f.Close()

	fi, err := f.Stat()
	if err != nil {
		return false
	}

	if mode := fi.Mode(); mode.IsDir() {
		return true
	}

	return false
}

func GetFilePathSeperator() string {
	osT := runtime.GOOS
	if osT == "windows" {
		return "\\"
	} else {
		return "/"
	}
}

func GetLastComponentOfFilePath(pathA string) string {
	if EndsWith(pathA, GetFilePathSeperator()) {
		return ""
	} else {
		return filepath.Base(pathA)
	}
}

func GetDirOfFilePath(pathA string) string {
	return filepath.Dir(pathA)
}

func RemoveFileExt(filePathA string) string {
	extT := filepath.Ext(filePathA)
	return filePathA[:len(filePathA)-len(extT)]
}

func GetFileExt(filePathA string) string {
	return filepath.Ext(filePathA)
}

func RemoveLastSubString(strA string, subStrA string) string {
	if EndsWith(strA, subStrA) {
		return strA[:len(strA)-len(subStrA)]
	}
	return strA
}

func AddLastSubString(strA string, subStrA string) string {
	if !EndsWith(strA, subStrA) {
		return strA + subStrA
	}
	return strA
}

func RemoveFile(filePathT string) error {
	if IsDirectory(filePathT) {
		return Errf("%v is a directory", filePathT)
	}

	errT := os.Remove(filePathT)

	if errT != nil {
		return errT
	}

	if IfFileExists(filePathT) {
		return Errf("failed to remove file: %v", filePathT)
	}

	return nil
}

func GenerateFileListInDir(dirA string, patternA string, verboseA bool) []string {
	strListT := make([]string, 0, 100)

	pathT, errT := filepath.Abs(dirA)

	if errT != nil {
		return nil
	}

	errT = filepath.Walk(pathT, func(path string, f os.FileInfo, err error) error {
		if verboseA {
			Pln(path)
		}

		if f == nil {
			return err
		}

		// Pl("pathT: %v -> path: %v", pathT, path)

		// if f.IsDir() { // && path != "." && path != pathT {
		if f.IsDir() {
			if path != "." && path != pathT {
				return filepath.SkipDir
			} else {
				return nil
			}
		}

		matchedT, errTI := filepath.Match(patternA, filepath.Base(path))
		if errTI == nil {
			if matchedT {
				strListT = append(strListT, path)
			}
		}

		return nil
	})

	if errT != nil {
		if verboseA {
			Pl("Search directory failed: %v", errT.Error())
		}

		return nil
	}

	return strListT
}

func GenerateFileListRecursively(dirA string, patternA string, verboseA bool) []string {
	strListT := make([]string, 0, 100)

	errT := filepath.Walk(dirA, func(path string, f os.FileInfo, err error) error {
		if verboseA {
			Pln(path)
		}

		if f == nil {
			return err
		}

		if f.IsDir() {
			return nil
		}

		matchedT, errTI := filepath.Match(patternA, filepath.Base(path))
		if errTI == nil {
			if matchedT {
				strListT = append(strListT, path)
				// Pl("append path: %v", path)
			}
		} else {
			// Pl("matching failed: %v", errTI.Error())
		}

		return nil
	})

	if errT != nil {
		Pl("Search directory failed: %v", errT.Error())
		return nil
	}

	return strListT
}

func GenerateFileListRecursivelyWithExclusive(dirA string, patternA string, exclusivePatternA string, verboseA bool) []string {
	strListT := make([]string, 0, 100)

	errT := filepath.Walk(dirA, func(path string, f os.FileInfo, err error) error {
		if verboseA {
			Pln(path)
		}

		if f == nil {
			return err
		}

		if f.IsDir() {
			return nil
		}

		matchedT, errTI := filepath.Match(patternA, filepath.Base(path))
		if errTI == nil {
			if matchedT {
				if exclusivePatternA != "" {
					matched2T, err2TI := filepath.Match(exclusivePatternA, filepath.Base(path))
					if err2TI == nil {
						if matched2T {
							return nil
						}
					}
				}

				strListT = append(strListT, path)
			}
		} else {
			Pl("matching failed: %v", errTI.Error())
		}

		return nil
	})

	if errT != nil {
		Pl("Search directory failed: %v", errT.Error())
		return nil
	}

	return strListT
}

func Ls(dirA string) []string {
	return GenerateFileListInDir(dirA, "*", false)
}

func Lsr(dirA string) []string {
	return GenerateFileListRecursivelyWithExclusive(dirA, "*", "", false)
}

func GetAvailableFileName(fileNameA string) string {
	fileNameT := fileNameA

	for i := 1; true; i++ {
		if !IfFileExists(fileNameT) {
			break
		}

		fileNameT = fmt.Sprintf("%s_%d%s", RemoveFileExt(fileNameA), i, filepath.Ext(fileNameA))
	}

	return fileNameT
}

// LoadStringFromFile 从文件中读取整个内容到字符串中
func LoadStringFromFile(fileNameA string) string {
	if !IfFileExists(fileNameA) {
		return GenerateErrorString("文件不存在")
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	return string(fileContentT)
}

// LoadStringFromFileWithDefault 从文件中读取整个内容到字符串中，出现问题时返回默认字符串
func LoadStringFromFileWithDefault(fileNameA string, defaultA string) string {
	if !IfFileExists(fileNameA) {
		return defaultA
	}

	fileT, errT := os.Open(fileNameA)
	if errT != nil {
		return defaultA
	}

	defer fileT.Close()

	fileContentT, errT := ioutil.ReadAll(fileT)
	if errT != nil {
		return defaultA
	}

	return string(fileContentT)
}

func LoadStringFromFileE(fileNameA string) (string, error) {
	if !IfFileExists(fileNameA) {
		return "", fmt.Errorf("file not exists")
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return "", err
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return "", err
	}

	return string(fileContentT), nil
}

func LoadStringFromFileB(fileNameA string) (string, bool) {
	if !IfFileExists(fileNameA) {
		return "file not exists", false
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return err.Error(), false
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return err.Error(), false
	}

	return string(fileContentT), true
}

// LoadBytes LoadBytes, no numA or numA < 0 indicates read all
func LoadBytes(fileNameA string, numA ...int) []byte {
	if !IfFileExists(fileNameA) {
		return nil
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return nil
	}

	defer fileT.Close()

	if numA == nil || len(numA) < 1 || numA[0] <= 0 {
		fileContentT, err := ioutil.ReadAll(fileT)
		if err != nil {
			return nil
		}

		return fileContentT
	}

	bufT := make([]byte, numA[0])
	nn, err := fileT.Read(bufT)
	if (err != nil) || (nn != len(bufT)) {
		return nil
	}

	return bufT
}

// LoadBytesFromFileE LoadBytes, no numA or numA[0] < 0 indicates read all
func LoadBytesFromFileE(fileNameA string, numA ...int) ([]byte, error) {
	if !IfFileExists(fileNameA) {
		return nil, Errf("file not exists")
	}

	fileT, errT := os.Open(fileNameA)
	if errT != nil {
		return nil, errT
	}

	defer fileT.Close()

	if numA == nil || len(numA) < 1 || numA[0] <= 0 {
		fileContentT, errT := ioutil.ReadAll(fileT)
		if errT != nil {
			return nil, errT
		}

		return fileContentT, nil
	}

	bufT := make([]byte, numA[0])

	nnT, errT := fileT.Read(bufT)
	if errT != nil {
		return nil, errT
	}

	if nnT != len(bufT) {
		return nil, Errf("read bytes not identical")
	}

	return bufT, nil
}

func SaveBytesToFile(bytesA []byte, fileA string) string {
	file, err := os.Create(fileA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	defer file.Close()

	wFile := bufio.NewWriter(file)
	_, err = wFile.Write(bytesA)

	if err != nil {
		return GenerateErrorString(err.Error())
	}

	wFile.Flush()

	return ""
}

// SaveStringToFile 保存字符串到文件
func SaveStringToFile(strA string, fileA string) string {
	file, err := os.Create(fileA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	defer file.Close()
	wFile := bufio.NewWriter(file)
	wFile.WriteString(strA)
	wFile.Flush()

	return ""
}

func SaveStringToFileE(strA string, fileA string) error {
	file, err := os.Create(fileA)
	if err != nil {
		return err
	}

	defer file.Close()
	wFile := bufio.NewWriter(file)
	wFile.WriteString(strA)
	wFile.Flush()

	return nil
}

func AppendStringToFile(strA string, fileA string) string {
	fileT, err := os.OpenFile(fileA, os.O_RDWR|os.O_CREATE|os.O_APPEND, 0666)
	if err != nil {
		//TXPlErr(err)
		return GenerateErrorString(err.Error())
	}

	writerT := bufio.NewWriter(fileT)

	writerT.WriteString(strA)

	writerT.Flush()

	defer fileT.Close()

	return ""
}

func LoadStringList(fileNameA string) ([]string, string) {
	if !IfFileExists(fileNameA) {
		return nil, "file not exists"
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return nil, err.Error()
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return nil, err.Error()
	}

	stringList := SplitLines(string(fileContentT))

	return stringList, ""
}

func LoadStringListFromFile(fileNameA string) ([]string, error) {
	if !IfFileExists(fileNameA) {
		return nil, fmt.Errorf("file not exists")
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return nil, err
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return nil, err
	}

	stringList := SplitLines(string(fileContentT))

	return stringList, nil
}

func LoadStringListBuffered(fileNameA string, trimA bool, skipEmptyA bool) ([]string, error) {
	if !IfFileExists(fileNameA) {
		return nil, Errf("file not exists", fileNameA)
	}

	fileT, errT := os.Open(fileNameA)
	if errT != nil {
		return nil, errT
	}

	defer fileT.Close()

	bufT := make([]string, 0, 1000)

	readerT := bufio.NewReader(fileT)

	for true {
		strT, errT := readerT.ReadString('\n')
		if errT != nil {
			if errT == io.EOF {
				if trimA {
					strT = Trim(strT)
				}

				if skipEmptyA {
					if strT != "" {
						bufT = append(bufT, strT)
					}
				} else {
					bufT = append(bufT, strT)
				}

			} else {
				return bufT, errT
			}

			break
		}

		if trimA {
			strT = Trim(strT)
		}

		if skipEmptyA {
			if strT != "" {
				bufT = append(bufT, strT)
			}
		} else {
			bufT = append(bufT, strT)
		}

	}

	return bufT, nil
}

func SaveStringList(strListA []string, fileA string) string {
	if strListA == nil {
		return GenerateErrorString("invalid parameter")
	}

	file, err := os.Create(fileA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	defer file.Close()

	wFile := bufio.NewWriter(file)
	wFile.WriteString(JoinLines(strListA))
	wFile.Flush()

	return ""
}

func SaveStringListWin(strListA []string, fileA string) string {
	if strListA == nil {
		return GenerateErrorString("invalid parameter")
	}

	file, err := os.Create(fileA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	defer file.Close()

	wFile := bufio.NewWriter(file)
	wFile.WriteString(JoinLinesBySeparator(strListA, "\r\n"))
	wFile.Flush()

	return ""
}

func SaveStringListBufferedByRange(strListA []string, fileA string, sepA string, startA int, endA int) string {
	if strListA == nil {
		return GenerateErrorString("invalid parameter")
	}

	if strListA == nil {
		return GenerateErrorString("empty list")
	}

	lenT := len(strListA)

	if startA < 0 || endA >= lenT {
		return GenerateErrorString("invalid range")
	}

	var errT error

	file, errT := os.Create(fileA)
	if errT != nil {
		return GenerateErrorString(errT.Error())
	}

	defer file.Close()

	wFile := bufio.NewWriter(file)

	for i := startA; i <= endA; i++ {
		_, errT = wFile.WriteString(strListA[i])
		if errT != nil {
			return GenerateErrorString(errT.Error())
		}

		if i != endA {
			_, errT = wFile.WriteString(sepA)
			if errT != nil {
				return GenerateErrorString(errT.Error())
			}
		}
	}

	wFile.Flush()

	return ""
}

func SaveStringListBuffered(strListA []string, fileA string, sepA string) string {
	if strListA == nil {
		return GenerateErrorString("invalid parameter")
	}

	if strListA == nil {
		return GenerateErrorString("empty list")
	}

	lenT := len(strListA)

	var errT error

	file, errT := os.Create(fileA)
	if errT != nil {
		return GenerateErrorString(errT.Error())
	}

	defer file.Close()

	wFile := bufio.NewWriter(file)

	for i := 0; i < lenT; i++ {
		_, errT = wFile.WriteString(strListA[i])
		if errT != nil {
			return GenerateErrorString(errT.Error())
		}

		if i != (lenT - 1) {
			_, errT = wFile.WriteString(sepA)
			if errT != nil {
				return GenerateErrorString(errT.Error())
			}
		}
	}

	wFile.Flush()

	return ""
}

func LoadStringListRemoveEmpty(fileNameA string) []string {
	if !IfFileExists(fileNameA) {
		return nil
	}

	fileT, err := os.Open(fileNameA)
	if err != nil {
		return nil
	}

	defer fileT.Close()

	fileContentT, err := ioutil.ReadAll(fileT)
	if err != nil {
		return nil
	}

	stringList := SplitLinesRemoveEmpty(string(fileContentT))

	return stringList
}

func LoadStringListAsMap(fileNameA string) map[string]int {
	rs, errStr := LoadStringList(fileNameA)

	if errStr != "" || rs == nil {
		return nil
	}

	rs1 := make(map[string]int, 0)
	for _, v := range rs {
		rs1[v] = 1
	}

	return rs1
}

func LoadStringListAsMapRemoveEmpty(fileNameA string) map[string]int {
	rs, errStr := LoadStringList(fileNameA)

	if errStr != "" || rs == nil {
		return nil
	}

	rs1 := make(map[string]int, 0)
	for _, v := range rs {
		if Trim(v) == "" {
			continue
		}

		rs1[v] = 1
	}

	return rs1
}

func LoadJSONMapStringFloat64ArrayFromFile(fileNameA string) map[string][]float64 {
	if !IfFileExists(fileNameA) {
		return nil
	}

	strT := LoadStringFromFile(fileNameA)
	if IsErrorString(strT) {
		return nil
	}

	return JSONToMapStringFloat64Array(strT)
}

// ReadLineFromBufioReader return result string, error and if reach EOF
func ReadLineFromBufioReader(readerA *bufio.Reader) (string, bool, error) {
	if readerA == nil {
		return "", false, Errf("nil reader")
	}

	strT, errT := readerA.ReadString('\n')

	if errT != nil {
		if errT == io.EOF {
			return strT, true, nil
		}

		return strT, false, errT
	}

	return strT, false, nil

}

func RestoreLineEnds(strA string, replacementA string) string {
	rs := strings.Replace(strA, replacementA, "\n", -1)
	return rs
}

// 双行列表相关 dual list related

func LoadDualLineList(fileNameA string) ([][]string, string) {
	rs, err := LoadStringList(fileNameA)

	if err != "" {
		return nil, err
	}

	lenT := len(rs) / 2

	bufT := make([][]string, lenT)

	var bufP []string

	for i := 0; i < lenT; i++ {
		bufP = make([]string, 2)

		bufP[0] = rs[i*2]
		bufP[1] = rs[i*2+1]

		bufT[i] = bufP
	}

	return bufT, ""
}

func SaveDualLineList(listA [][]string, fileNameA string) string {
	if listA == nil {
		return GenerateErrorString("nil list")
	}

	lenT := len(listA)

	bufT := make([]string, lenT*2)

	for i := 0; i < lenT; i++ {
		bufT[i*2] = listA[i][0]
		bufT[i*2+1] = listA[i][1]
	}

	return SaveStringList(bufT, fileNameA)
}

func RemoveDuplicateInDualLineList(listA [][]string) [][]string {
	if listA == nil {
		return nil
	}

	listT := listA

	i := 0

	for true {
		lenT := len(listT)

		if lenT <= 1 {
			break
		}

		if i >= lenT {
			break
		}

		found := false

		for j := i + 1; j < lenT; j++ {
			if listT[j][0] == listT[i][0] {
				found = true
				break
			}
		}

		if found {
			listT = append(listT[:i], listT[i+1:]...)
			continue
		}

		i++
	}

	return listT
}

func AppendDualLineList(listA [][]string, fileNameA string) string {
	if listA == nil {
		return GenerateErrorString("nil list")
	}

	var listT [][]string
	var err string

	if IfFileExists(fileNameA) {
		listT, err = LoadDualLineList(fileNameA)

		if err != "" {
			return GenerateErrorStringF("failed to open file: %v", err)
		}

		listT = RemoveDuplicateInDualLineList(append(listT, listA...))

		// lenTiA := len(listA)
		// lenTi := len(listT)

		// for i := 0; i < lenTiA; i++ {
		// 	found := -1

		// 	for j := 0; j < lenTi; j++ {
		// 		if listA[i][0] == listT[j][0] {
		// 			found = j
		// 			break
		// 		}
		// 	}

		// 	if found < 0 {
		// 		listT = append(listT, listA[i])
		// 	} else {
		// 		listT[found][0] = listA[i][0]
		// 		listT[found][1] = listA[i][1]
		// 	}
		// }
	} else {
		listT = listA
	}

	lenT := len(listT)

	bufT := make([]string, lenT*2)

	for i := 0; i < lenT; i++ {
		bufT[i*2] = listT[i][0]
		bufT[i*2+1] = listT[i][1]
	}

	return SaveStringList(bufT, fileNameA)
}

// SimpleMap related
// in a simplemap structure, key/value pairs are in form as KEY=VALUE
// "=" in keys should be replaced as `EQ`
// line-ends in values such as "\n" should be replaced as #CR#
// comments could be used after ####

func LoadSimpleMapFromFile(fileNameA string) map[string]string {
	if !IfFileExists(fileNameA) {
		return nil
	}

	strListT, _ := LoadStringList(fileNameA)

	if strListT == nil {
		return nil
	}

	mapT := make(map[string]string)
	for i := range strListT {
		lineT := strListT[i]
		lineT = strings.SplitN(lineT, "####", 2)[0]
		lineListT := strings.SplitN(lineT, "=", 2)
		if (lineListT == nil) || (len(lineListT) < 2) {
			continue
		}
		mapT[Replace(lineListT[0], "`EQ`", "=")] = RestoreLineEnds(lineListT[1], "#CR#")
	}

	return mapT
}

func LoadSimpleMapFromFileE(fileNameA string) (map[string]string, error) {
	if !IfFileExists(fileNameA) {
		return nil, fmt.Errorf("file not exists")
	}

	fc, errT := LoadStringFromFileE(fileNameA)

	if errT != nil {
		return nil, errT
	}

	return LoadSimpleMapFromStringE(fc)
}

func SimpleMapToString(mapA map[string]string) string {
	strListT := make([]string, 0, len(mapA)+1)

	var kk string
	for k, v := range mapA {
		kk = Replace(k, "=", "`EQ`")
		strListT = append(strListT, kk+"="+ReplaceLineEnds(v, "#CR#"))
	}

	return JoinLines(strListT)
}

func LoadSimpleMapFromString(strA string) map[string]string {
	strListT := SplitLines(strA)

	if strListT == nil {
		return nil
	}

	mapT := make(map[string]string)
	for i := range strListT {
		lineT := strListT[i]

		lineT = strings.SplitN(lineT, "####", 2)[0]

		lineListT := strings.SplitN(lineT, "=", 2)
		if (lineListT == nil) || (len(lineListT) < 2) {
			continue
		}
		mapT[Replace(lineListT[0], "`EQ`", "=")] = RestoreLineEnds(lineListT[1], "#CR#")
	}

	return mapT
}

func LoadSimpleMapFromStringE(strA string) (map[string]string, error) {
	strListT := SplitLines(strA)

	if strListT == nil {
		return nil, fmt.Errorf("string nil")
	}

	mapT := make(map[string]string)
	for i := range strListT {
		lineT := strListT[i]

		lineT = strings.SplitN(lineT, "####", 2)[0]

		lineListT := strings.SplitN(lineT, "=", 2)
		if (lineListT == nil) || (len(lineListT) < 2) {
			continue
		}
		mapT[Replace(lineListT[0], "`EQ`", "=")] = RestoreLineEnds(lineListT[1], "#CR#")
	}

	return mapT, nil
}

func ReplaceLineEnds(strA string, replacementA string) string {
	rs := strings.Replace(strA, "\r", "", -1)
	rs = strings.Replace(rs, "\n", replacementA, -1)
	return rs
}

func SaveSimpleMapToFile(mapA map[string]string, fileA string) string {
	fileT, errT := os.Create(fileA)
	if errT != nil {
		return GenerateErrorString(errT.Error())
	}

	defer fileT.Close()

	wFile := bufio.NewWriter(fileT)

	var kk string

	if mapA != nil {
		for k, v := range mapA {
			kk = Replace(k, "=", "`EQ`")
			wFile.WriteString(kk + "=" + ReplaceLineEnds(v, "#CR#") + "\n")
		}
	}

	wFile.Flush()

	return ""
}

func AppendSimpleMapFromFile(mapA map[string]string, fileNameA string) string {
	if !IfFileExists(fileNameA) {
		return "file not exists"
	}

	strListT, errStrT := LoadStringList(fileNameA)

	if errStrT != "" {
		return "fail to load file content"
	}

	for i := range strListT {
		lineT := strListT[i]

		lineT = strings.SplitN(lineT, "####", 2)[0]

		lineListT := strings.SplitN(lineT, "=", 2)
		if (lineListT == nil) || (len(lineListT) < 2) {
			continue
		}

		mapA[Replace(lineListT[0], "`EQ`", "=")] = RestoreLineEnds(lineListT[1], "#CR#")
	}

	return ""
}

func LoadSimpleMapFromDir(dirA string) map[string]string {
	if !IfFileExists(dirA) {
		return nil
	}

	if !IsDirectory(dirA) {
		return nil
	}

	mapT := make(map[string]string)
	files := GenerateFileListRecursively(dirA, "*.txt", false)
	if files == nil {
		return nil
	}

	for _, v := range files {
		AppendSimpleMapFromFile(mapT, v)
	}

	return mapT
}

// GetLinesFromFile at least will return []string{}, avoid nil result
func GetLinesFromFile(fileNameA string, startA int, endA int, optionsA ...string) ([]string, error) {
	failForRangeT := false

	if !IsNilOrEmpty(optionsA) {
		if IfSwitchExistsWhole(optionsA, "-index") {
			startA++
			endA++
		}

		if IfSwitchExistsWhole(optionsA, "-range") {
			failForRangeT = true
		}
	}

	if failForRangeT {
		if startA < 1 {
			return []string{}, Errf("invalid start index: %v", startA)
		}
	}

	f, errT := os.Open(fileNameA)
	if errT != nil {
		return []string{}, Errf("failed to open file: %v", errT)
	}

	defer f.Close()

	r := bufio.NewReader(f)

	i := 0

	var bufT = make([]string, 0, endA-startA+2)

	for true {
		line, errT := r.ReadString('\n')

		i++

		// pl("process %v", i)

		if i < startA {
			continue
		}

		if i > endA {
			break
		}

		if errT != nil {
			if errT == io.EOF {
				if failForRangeT {
					return bufT, Errf("invalid end index: %v", endA)
				}

				break
			}

			return bufT, Errf("failed to read content: %v, line: %v", errT, line)
		}

		// pl("%v", line)
		bufT = append(bufT, strings.TrimRight(line, "\r\n"))

	}

	return bufT, nil
}

// 编码解码相关 encode/decode

func EncodeToBase64(bufA []byte) string {
	return base64.StdEncoding.EncodeToString(bufA)
}

func EncodeHTML(strA string) string {
	return html.EscapeString(strA)
}

func DecodeHTML(strA string) string {
	return html.UnescapeString(strA)
}

func DecodeFromBase64(strA string) ([]byte, error) {
	return base64.StdEncoding.DecodeString(strA)
}

// EncodeToXMLString 转换字符串XML格式编码的字符串，例如：字符串“<as>\"!sdsdsgfde345344对方对方对法国</as>” 会编码为 “&lt;as&gt;&#34;!sdsdsgfde345344对方对方对法国&lt;/as&gt;”
func EncodeToXMLString(strA string) string {
	var bufT strings.Builder

	errT := xml.EscapeText(&bufT, []byte(strA))

	if errT != nil {
		return strA
	}

	return bufT.String()
}

// ToJSON use fast method
func ToJSON(objA interface{}) (string, error) {
	// var json = jsoniter.ConfigCompatibleWithStandardLibrary
	// var json = jsoniter.ConfigFastest
	rs, errT := jsoniter.Marshal(objA)

	// if errT != nil {
	// 	return GenerateErrorString(errT.Error())
	// }

	return string(rs), errT
}

func ToJSONX(objA interface{}, optsA ...string) string {
	var errT error

	ifDefaultT := IfSwitchExists(optsA, "-default=")

	indentT := false
	if IfSwitchExistsWhole(optsA, "-indent") {
		indentT = true
	}

	var jsonT jsoniter.API

	if optsA == nil || len(optsA) < 1 {
		jsonT = jsoniter.ConfigDefault
	} else if IfSwitchExistsWhole(optsA, "-sort") {
		jsonT = jsoniter.ConfigCompatibleWithStandardLibrary
	} else if IfSwitchExistsWhole(optsA, "-fast") {
		jsonT = jsoniter.ConfigFastest
	} else {
		jsonT = jsoniter.ConfigDefault
	}

	var rs []byte

	if indentT {
		rs, errT = jsonT.MarshalIndent(objA, "", "  ")
	} else {
		rs, errT = jsonT.Marshal(objA)

	}

	if errT != nil {
		if ifDefaultT {
			return GetSwitchWithDefaultValue(optsA, "-default=", GenerateErrorString(errT.Error()))
		}

		return GenerateErrorString(errT.Error())
	}

	return string(rs)
}

func ToJSONWithDefault(objA interface{}, defaultA string) string {
	rs, errT := jsoniter.Marshal(objA)

	if errT != nil {
		return defaultA
	}

	return string(rs)
}

// ToJSONIndent use fast method
func ToJSONIndent(objA interface{}) (string, error) {
	// var json = jsoniter.ConfigCompatibleWithStandardLibrary
	// var json = jsoniter.ConfigFastest
	rs, errT := jsoniter.MarshalIndent(objA, "", "  ")

	// if errT != nil {
	// 	return GenerateErrorString(errT.Error())
	// }

	return string(rs), errT
}

func ToJSONIndentWithDefault(objA interface{}, defaultA string) string {
	rs, errT := jsoniter.MarshalIndent(objA, "", "  ")

	if errT != nil {
		return defaultA
	}

	return string(rs)
}

// FromJson fast JSON decode
func FromJSON(jsonA string) (interface{}, error) {
	var rs interface{}

	errT := jsoniter.Unmarshal([]byte(jsonA), &rs)

	if errT != nil {
		return nil, errT
	}

	return rs, nil
}

func FromJSONWithDefault(jsonA string, defaultA interface{}) interface{} {
	var rs interface{}

	errT := jsoniter.Unmarshal([]byte(jsonA), &rs)

	if errT != nil {
		return defaultA
	}

	return rs
}

func MSSFromJSON(jsonA string) (map[string]string, error) {
	var rs map[string]string

	errT := jsoniter.Unmarshal([]byte(jsonA), &rs)

	if errT != nil {
		return nil, errT
	}

	return rs, nil
}

func LoadJSONFromFile(filePathA string, bufA interface{}) error {
	fcT, errT := LoadBytesFromFileE(filePathA, -1)

	if errT != nil {
		return errT
	}

	errT = jsoniter.Unmarshal(fcT, bufA)

	if errT != nil {
		return errT
	}

	return nil

}

func LoadJSONFromString(strA string, bufA interface{}) error {
	errT := jsoniter.Unmarshal([]byte(strA), bufA)

	if errT != nil {
		return errT
	}

	return nil

}

func SaveJSONToFile(objA interface{}, filePathA string) error {
	rs, errT := jsoniter.Marshal(objA)

	if errT != nil {
		return errT
	}

	errT = SaveStringToFileE(string(rs), filePathA)

	return errT
}

func SaveJSONIndentToFile(objA interface{}, filePathA string) error {
	rs, errT := jsoniter.MarshalIndent(objA, "", "  ")

	if errT != nil {
		return errT
	}

	errT = SaveStringToFileE(string(rs), filePathA)

	return errT
}

func LoadMSSFromJSONFile(filePathA string) (map[string]string, error) {
	fcT, errT := LoadStringFromFileE(filePathA)

	if errT != nil {
		return nil, errT
	}

	var rs map[string]string

	errT = jsoniter.Unmarshal([]byte(fcT), &rs)

	if errT != nil {
		return nil, errT
	}

	return rs, nil
}

func SaveMSSToJSONFile(mapA map[string]string, filePathA string) error {
	rs1, errT := ToJSONIndent(mapA)

	if errT != nil {
		return errT
	}

	rs := SaveStringToFileE(rs1, filePathA)

	return rs

}

// GetJSONNode return jsoniter.Any type as interface{}
func GetJSONNode(jsonA string, pathA ...interface{}) interface{} {
	aryT := make([]interface{}, 0, len(pathA))

	var typeT reflect.Type
	for _, v := range pathA {
		typeT = reflect.TypeOf(v)

		if typeT.Kind() == reflect.Int64 {
			aryT = append(aryT, int(v.(int64)))
		} else if typeT.Kind() == reflect.String && v.(string) == "*" {
			aryT = append(aryT, int32('*'))
		} else {
			aryT = append(aryT, v)
		}
	}

	rs := jsoniter.Get([]byte(jsonA), aryT...)

	return rs.GetInterface()
}

// GetJSONSubNode return jsoniter.Any type as interface{}
func GetJSONSubNode(jsonNodeA jsoniter.Any, pathA ...interface{}) interface{} {
	aryT := make([]interface{}, 0, len(pathA))

	var typeT reflect.Type
	for _, v := range pathA {
		typeT = reflect.TypeOf(v)

		if typeT.Kind() == reflect.Int64 {
			aryT = append(aryT, int(v.(int64)))
		} else if typeT.Kind() == reflect.String && v.(string) == "*" {
			aryT = append(aryT, int32('*'))
		} else {
			aryT = append(aryT, v)
		}
	}

	rs := jsonNodeA.Get(aryT...)

	return rs.GetInterface()
}

// GetJSONNodeAny return jsoniter.Any type
// func Get(data []byte, path ...interface{}) Any takes interface{} as path. If string, it will lookup json map. If int, it will lookup json array. If '*', it will map to each element of array or each key of map.
func GetJSONNodeAny(jsonA string, pathA ...interface{}) jsoniter.Any {
	aryT := make([]interface{}, 0, len(pathA))

	var typeT reflect.Type
	for _, v := range pathA {
		typeT = reflect.TypeOf(v)

		if typeT.Kind() == reflect.Int64 {
			aryT = append(aryT, int(v.(int64)))
		} else if typeT.Kind() == reflect.String && v.(string) == "*" {
			aryT = append(aryT, int32('*'))
		} else {
			aryT = append(aryT, v)
		}
	}

	rs := jsoniter.Get([]byte(jsonA), aryT...)

	return rs
}

func GetJSONSubNodeAny(jsonNodeA jsoniter.Any, pathA ...interface{}) jsoniter.Any {
	aryT := make([]interface{}, 0, len(pathA))

	var typeT reflect.Type
	for _, v := range pathA {
		typeT = reflect.TypeOf(v)

		if typeT.Kind() == reflect.Int64 {
			aryT = append(aryT, int(v.(int64)))
		} else if typeT.Kind() == reflect.String && v.(string) == "*" {
			aryT = append(aryT, int32('*'))
		} else {
			aryT = append(aryT, v)
		}
	}

	rs := jsonNodeA.Get(aryT...)

	return rs
}

// ObjectToJSON 任意对象转换为JSON字符串
func ObjectToJSON(objA interface{}) string {
	bufferT, errT := json.Marshal(objA)
	if errT != nil {
		return GenerateErrorStringF("failed: %s", errT.Error())
	}

	return string(bufferT)
}

func ObjectToJSONIndent(objA interface{}) string {
	bufferT, errT := json.MarshalIndent(objA, "", "")
	if errT != nil {
		return GenerateErrorStringF("failed: %s", errT.Error())
	}

	return string(bufferT)
}

func JSONToMapStringFloat64Array(objStrA string) map[string][]float64 {
	var rMapT map[string][]float64
	errT := json.Unmarshal([]byte(objStrA), &rMapT)
	if errT != nil {
		return nil
	}

	return rMapT
}

func JSONToMapStringString(objStrA string) map[string]string {
	var rMapT map[string]string
	errT := json.Unmarshal([]byte(objStrA), &rMapT)
	if errT != nil {
		return nil
	}

	return rMapT
}

func JSONToObject(objStrA string) interface{} {
	var rs interface{}
	errT := json.Unmarshal([]byte(objStrA), &rs)
	if errT != nil {
		return nil
	}

	return rs
}

func JSONToObjectE(objStrA string) (interface{}, error) {
	var rs interface{}

	errT := json.Unmarshal([]byte(objStrA), &rs)
	if errT != nil {
		return nil, errT
	}

	return rs, nil
}

func SafelyGetStringForKeyWithDefault(mapA map[string]string, keyA string, defaultA string) string {
	if mapA == nil {
		return defaultA
	}

	v, ok := mapA[keyA]
	if !ok {
		return defaultA
	}

	return v
}

func GetMSIStringWithDefault(mapA map[string]interface{}, keyA string, defaultA string) (result string) {
	defer func() {
		r := recover()

		if r != nil {
			result = defaultA
			return
		}
	}()

	if mapA == nil {
		result = defaultA
		return
	}

	v, ok := mapA[keyA]
	if !ok {
		result = defaultA
		return
	}

	result = v.(string)
	return
}

func SafelyGetFloat64ForKeyWithDefault(mapA map[string]string, keyA string, defaultA float64) float64 {
	if mapA == nil {
		return defaultA
	}

	v, ok := mapA[keyA]
	if !ok {
		return defaultA
	}

	return StrToFloat64WithDefaultValue(v, defaultA)
}

func SafelyGetIntForKeyWithDefault(mapA map[string]string, keyA string, defaultA int) int {
	if mapA == nil {
		return defaultA
	}

	v, ok := mapA[keyA]
	if !ok {
		return defaultA
	}

	return StrToIntWithDefaultValue(v, defaultA)
}

func JSONToStringArray(objStrA string) []string {
	var rArrayT []string
	errT := json.Unmarshal([]byte(objStrA), &rArrayT)
	if errT != nil {
		return nil
	}

	return rArrayT
}

func EncodeStringSimple(strA string) string {
	lenT := len(strA)

	hexCount := 0
	for i := 0; i < lenT; i++ {
		v := strA[i]
		if !(((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z'))) {
			// Prl("v=%v, %v, %v", v, 'a', (((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z'))))
			hexCount++
		}
	}

	if hexCount == 0 {
		return strA
	}

	t := make([]byte, lenT+2*hexCount)
	j := 0

	for i := 0; i < lenT; i++ {
		switch v := strA[i]; {
		case !(((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z'))):
			t[j] = '%'
			t[j+1] = "0123456789ABCDEF"[v>>4]
			t[j+2] = "0123456789ABCDEF"[v&15]
			j += 3
		default:
			t[j] = strA[i]
			j++
		}
	}

	return string(t)
}

func EncodeStringUnderline(strA string) string {
	lenT := len(strA)

	var sbuf strings.Builder

	tableStrT := "0123456789ABCDEF"

	for i := 0; i < lenT; i++ {
		v := strA[i]

		if !(((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z')) || ((v >= 'A') && (v <= 'Z'))) {
			sbuf.WriteByte('_')
			sbuf.WriteByte(tableStrT[v>>4])
			sbuf.WriteByte(tableStrT[v&15])
		} else {
			sbuf.WriteByte(strA[i])
		}
	}

	return sbuf.String()
}

func EncodeStringCustom(strA string, paddingA byte) string {
	if paddingA == 0 {
		paddingA = '_'
	}

	lenT := len(strA)

	var sbuf strings.Builder

	tableStrT := "0123456789ABCDEF"

	for i := 0; i < lenT; i++ {
		v := strA[i]

		if !(((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z')) || ((v >= 'A') && (v <= 'Z'))) {
			sbuf.WriteByte(paddingA)
			sbuf.WriteByte(tableStrT[v>>4])
			sbuf.WriteByte(tableStrT[v&15])
		} else {
			sbuf.WriteByte(strA[i])
		}
	}

	return sbuf.String()
}

func EncodeStringCustomEx(strA string, paddingsA ...byte) string {
	var paddingA byte

	if paddingsA == nil || len(paddingsA) == 0 {
		paddingA = '_'
	} else {
		paddingA = paddingsA[0]
	}

	lenT := len(strA)

	var sbuf strings.Builder

	tableStrT := "0123456789ABCDEF"

	for i := 0; i < lenT; i++ {
		v := strA[i]

		if !(((v >= '0') && (v <= '9')) || ((v >= 'a') && (v <= 'z'))) {
			sbuf.WriteByte(paddingA)
			sbuf.WriteByte(tableStrT[v>>4])
			sbuf.WriteByte(tableStrT[v&15])
		} else {
			sbuf.WriteByte(strA[i])
		}
	}

	return sbuf.String()
}

func ishex(c byte) bool {
	switch {
	case '0' <= c && c <= '9':
		return true
	case 'a' <= c && c <= 'f':
		return true
	case 'A' <= c && c <= 'F':
		return true
	}
	return false
}

func unhex(c byte) byte {
	switch {
	case '0' <= c && c <= '9':
		return c - '0'
	case 'a' <= c && c <= 'f':
		return c - 'a' + 10
	case 'A' <= c && c <= 'F':
		return c - 'A' + 10
	}
	return 0
}

func DecodeStringSimple(s string) string {
	// Count %, check that they're well-formed.
	n := 0
	// hasPlus := false

	for i := 0; i < len(s); {
		switch s[i] {
		case '%':
			n++

			if i+2 >= len(s) || !ishex(s[i+1]) || !ishex(s[i+2]) {
				// s = s[i:]
				// if len(s) > 3 {
				// 	s = s[:3]
				// }
				return s
			}

			i += 3

		default:
			i++
		}
	}

	// if n == 0 && !hasPlus {
	// 	return GenerateErrorString("invalid format")
	// }

	t := make([]byte, len(s)-2*n)
	j := 0
	for i := 0; i < len(s); {
		switch s[i] {
		case '%':
			t[j] = unhex(s[i+1])<<4 | unhex(s[i+2])
			j++
			i += 3
		default:
			t[j] = s[i]
			j++
			i++
		}
	}
	return string(t)
}

func DecodeStringUnderline(s string) string {
	var bufT strings.Builder

	lenT := len(s)

	for i := 0; i < lenT; {
		if s[i] == '_' {
			if i+2 >= lenT {
				return s
			}
			bufT.WriteByte(unhex(s[i+1])<<4 | unhex(s[i+2]))

			i += 3
		} else {
			bufT.WriteByte(s[i])
			i++
		}
	}

	return bufT.String()
}

func DecodeStringCustom(s string, paddingsA ...byte) string {
	var paddingA byte

	if paddingsA == nil || len(paddingsA) == 0 {
		paddingA = '_'
	} else {
		paddingA = paddingsA[0]
	}

	var bufT strings.Builder

	lenT := len(s)

	for i := 0; i < lenT; {
		if s[i] == paddingA {
			if i+2 >= lenT {
				return s
			}
			bufT.WriteByte(unhex(s[i+1])<<4 | unhex(s[i+2]))

			i += 3
		} else {
			bufT.WriteByte(s[i])
			i++
		}
	}

	return bufT.String()
}

func MD5Encrypt(strA string) string {
	tmpb := md5.Sum([]byte(strA))

	tmpbb := tmpb[:]

	return hex.EncodeToString(tmpbb)
}

// 加密解密相关

func BytesToHex(bufA []byte) string {
	return strings.ToUpper(hex.EncodeToString(bufA))
}

func HexToBytes(strA string) []byte {
	buf, err := hex.DecodeString(strA)
	if err != nil {
		return nil
	}

	return buf
}

// HexToInt return -1 if failed
func HexToInt(strA string) int {
	buf, err := hex.DecodeString(strA)
	if err != nil {
		return -1
	}

	lenT := len(buf)

	m := 1

	rs := 0

	for i := lenT - 1; i >= 0; i-- {
		rs += int(buf[i]) * m

		m *= 256
	}

	return rs

}

func GetRandomByte() byte {
	Randomize()

	randT := rand.Intn(256)

	return byte(randT)
}

func EncryptDataByTXDEE(srcDataA []byte, codeA string) []byte {
	if srcDataA == nil {
		return nil
	}

	dataLen := len(srcDataA)
	if dataLen < 1 {
		return srcDataA
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	bufB := make([]byte, dataLen+4)

	bufB[0] = GetRandomByte()
	bufB[1] = GetRandomByte()

	for i := 0; i < dataLen; i++ {
		bufB[2+i] = srcDataA[i] + codeBytes[i%codeLen] + byte(i+1) + bufB[1]
	}

	bufB[dataLen+4-2] = GetRandomByte()
	bufB[dataLen+4-1] = GetRandomByte()

	return bufB
}

func SumBytes(srcDataA []byte) byte {
	if srcDataA == nil {
		return 0
	}

	lenT := len(srcDataA)

	var b byte = 0

	for i := 0; i < lenT; i++ {
		b += srcDataA[i]
	}

	return b
}

func EncryptDataByTXDEF(srcDataA []byte, codeA string) []byte {
	if srcDataA == nil {
		return nil
	}

	dataLen := len(srcDataA)
	if dataLen < 1 {
		return srcDataA
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	sumT := int(SumBytes(codeBytes))

	addLenT := int((sumT % 5) + 2)
	encIndexT := sumT % addLenT
	// Plvsr(addLenT, encIndexT)

	bufB := make([]byte, dataLen+addLenT)

	for i := 0; i < addLenT; i++ {
		bufB[i] = GetRandomByte()
	}

	for i := 0; i < dataLen; i++ {
		bufB[addLenT+i] = srcDataA[i] + codeBytes[i%codeLen] + byte(i+1) + bufB[encIndexT]
	}

	return bufB
}

const TXDEF_BUFFER_LEN = 1000

func EncryptStreamByTXDEF(readerA io.Reader, codeA string, writerA io.Writer) error {
	if readerA == nil {
		return Errf("reader nil")
	}

	if writerA == nil {
		return Errf("writer nil")
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	// if codeLen > TXDEF_BUFFER_LEN {
	// 	return Errf("code length longer than buffer length")
	// }

	sumT := int(SumBytes(codeBytes))

	addLenT := int((sumT % 5) + 2)
	encIndexT := sumT % addLenT
	// Plvsr(addLenT, encIndexT)

	var idxByte byte

	addBufT := make([]byte, addLenT)

	for i := 0; i < addLenT; i++ {
		addBufT[i] = GetRandomByte()

		if i == encIndexT {
			idxByte = addBufT[i]
		}

	}

	_, errT := writerA.Write(addBufT)

	if errT != nil {
		return errT
	}

	bufArrayT := make([]byte, 0, TXDEF_BUFFER_LEN+8)

	bufT := bytes.NewBuffer(bufArrayT)

	bufArrayReaderT := make([]byte, TXDEF_BUFFER_LEN)

	i := 0

	breakFlagT := false

	for {
		bytesT, errT := readerA.Read(bufArrayReaderT)

		if errT != nil {
			if errT == io.EOF {
				breakFlagT = true
			} else {
				return errT
			}

		}

		for j := 0; j < bytesT; j++ {
			bufT.WriteByte(bufArrayReaderT[j] + codeBytes[i%codeLen] + byte(i+1) + idxByte)

			i++

			if bufT.Len() >= TXDEF_BUFFER_LEN {
				_, errT := writerA.Write(bufT.Bytes()[:TXDEF_BUFFER_LEN])

				if errT != nil {
					return errT
				}

				bufT.Reset()
			}
		}

		if breakFlagT {
			if bufT.Len() > 0 {
				_, errT := writerA.Write(bufT.Bytes())

				if errT != nil {
					return errT
				}

				bufT.Reset()
			}

			break
		}
	}

	return nil
}

func DecryptStreamByTXDEF(readerA io.Reader, codeA string, writerA io.Writer) error {
	if readerA == nil {
		return Errf("reader nil")
	}

	if writerA == nil {
		return Errf("writer nil")
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	sumT := int(SumBytes(codeBytes))

	addLenT := int((sumT % 5) + 2)
	encIndexT := sumT % addLenT
	// Plvsr(addLenT, encIndexT)

	var idxByte byte

	addBufT := make([]byte, addLenT)

	bytesT, errT := readerA.Read(addBufT)

	if errT != nil {
		if errT != io.EOF {
			return errT
		}
	}

	if bytesT != addLenT {
		return Errf("failed to read header")
	}

	idxByte = addBufT[encIndexT]

	bufArrayT := make([]byte, 0, TXDEF_BUFFER_LEN+8)

	bufT := bytes.NewBuffer(bufArrayT)

	bufArrayReaderT := make([]byte, TXDEF_BUFFER_LEN)

	i := 0

	breakFlagT := false

	for {
		bytesT, errT := readerA.Read(bufArrayReaderT)

		if errT != nil {
			if errT == io.EOF {
				breakFlagT = true
			} else {
				return errT
			}

		}

		for j := 0; j < bytesT; j++ {
			bufT.WriteByte(bufArrayReaderT[j] - codeBytes[i%codeLen] - byte(i+1) - idxByte)

			i++

			if bufT.Len() >= TXDEF_BUFFER_LEN {
				_, errT := writerA.Write(bufT.Bytes()[:TXDEF_BUFFER_LEN])

				if errT != nil {
					return errT
				}

				bufT.Reset()
			}
		}

		if breakFlagT {
			if bufT.Len() > 0 {
				_, errT := writerA.Write(bufT.Bytes())

				if errT != nil {
					return errT
				}

				bufT.Reset()
			}

			break
		}
	}

	return nil
}

func DecryptDataByTXDEE(srcDataA []byte, codeA string) []byte {
	if srcDataA == nil {
		return nil
	}

	dataLen := len(srcDataA)
	if dataLen < 4 {
		return nil
	}

	dataLen -= 4

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	bufB := make([]byte, dataLen)

	for i := 0; i < dataLen; i++ {
		bufB[i] = srcDataA[2+i] - codeBytes[i%codeLen] - byte(i+1) - srcDataA[1]
	}

	return bufB
}

func DecryptDataByTXDEF(srcDataA []byte, codeA string) []byte {
	if srcDataA == nil {
		return nil
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	codeBytes := []byte(codeT)
	codeLen := len(codeBytes)

	sumT := int(SumBytes(codeBytes))

	addLenT := int((sumT % 5) + 2)
	encIndexT := sumT % addLenT

	dataLen := len(srcDataA)
	if dataLen < addLenT {
		return nil
	}

	dataLen -= addLenT

	bufB := make([]byte, dataLen)

	for i := 0; i < dataLen; i++ {
		bufB[i] = srcDataA[addLenT+i] - codeBytes[i%codeLen] - byte(i+1) - srcDataA[encIndexT]
	}

	return bufB
}

func EncryptStringByTXTE(strA string, codeA string) string {
	if strA == "" {
		return ""
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	sBufT := []byte(strA)
	codeButT := []byte(codeT)

	sDataLen := len(sBufT)
	codeLenT := len(codeButT)

	dBufT := make([]byte, sDataLen)

	for i := 0; i < sDataLen; i++ {
		dBufT[i] = sBufT[i] + codeButT[i%codeLenT] + byte(i+1)
	}

	return strings.ToUpper(hex.EncodeToString(dBufT))

}

func DecryptStringByTXTE(strA string, codeA string) string {
	if strA == "" {
		return ""
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	sBufT, errT := hex.DecodeString(strA)
	if errT != nil {
		return ""
	}
	codeButT := []byte(codeT)

	sDataLen := len(sBufT)
	codeLenT := len(codeButT)

	dBufT := make([]byte, sDataLen)

	for i := 0; i < sDataLen; i++ {
		dBufT[i] = sBufT[i] - codeButT[i%codeLenT] - byte(i+1)
	}

	return string(dBufT)

}

func EncryptStringByTXDEE(strA, codeA string) string {
	if strA == "" {
		return ""
	}

	dataDT := EncryptDataByTXDEE([]byte(strA), codeA)
	if dataDT == nil {
		return GenerateErrorStringF("encrypting failed")
	}

	return strings.ToUpper(hex.EncodeToString(dataDT))
}

func DecryptStringByTXDEE(strA, codeA string) string {
	if strA == "" {
		return ""
	}

	var sBufT []byte
	var errT error

	if StartsWith(strA, "740404") {
		sBufT, errT = hex.DecodeString(strA[6:])
	} else {
		sBufT, errT = hex.DecodeString(strA)
	}

	if errT != nil {
		return GenerateErrorStringF("decrypting failed")
	}

	dataDT := DecryptDataByTXDEE(sBufT, codeA)
	if dataDT == nil {
		return GenerateErrorStringF("decrypting failed")
	}

	return string(dataDT)
}

func EncryptStringByTXDEF(strA, codeA string) string {
	if strA == "" {
		return ""
	}

	dataDT := EncryptDataByTXDEF([]byte(strA), codeA)
	if dataDT == nil {
		return GenerateErrorStringF("encrypting failed")
	}

	return strings.ToUpper(hex.EncodeToString(dataDT))
}

func DecryptStringByTXDEF(strA, codeA string) string {
	if strA == "" {
		return ""
	}

	var sBufT []byte
	var errT error

	if StartsWith(strA, "740404") {
		sBufT, errT = hex.DecodeString(strA[6:])
	} else if StartsWith(strA, "//TXDEF#") {
		sBufT, errT = hex.DecodeString(strA[8:])
	} else {
		sBufT, errT = hex.DecodeString(strA)
	}

	if errT != nil {
		return GenerateErrorStringF("decrypting failed: %v", errT)
	}

	dataDT := DecryptDataByTXDEF(sBufT, codeA)
	if dataDT == nil {
		return GenerateErrorStringF("decrypting failed")
	}

	return string(dataDT)
}

func EncryptFileByTXDEF(fileNameA, codeA, outputFileA string) error {
	if !IfFileExists(fileNameA) {
		return Errf("")
	}

	srcStatT, errT := os.Stat(fileNameA)
	if errT != nil {
		return Errf("error os.Stat src %s: %s", fileNameA, errT.Error())
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	outputFileT := outputFileA
	if outputFileT == "" {
		outputFileT = fileNameA + ".txdef"
	}

	fileContenT, errT := ioutil.ReadFile(fileNameA)
	if errT != nil {
		return errT
	}

	writeContentT := EncryptDataByTXDEF(fileContenT, codeT)
	if writeContentT == nil {
		return Errf("encrypt data failed")
	}

	errT = ioutil.WriteFile(outputFileT, writeContentT, srcStatT.Mode())
	if errT != nil {
		return errT
	}

	return nil
}

func EncryptFileByTXDEFWithHeader(fileNameA, codeA, outputFileA string) error {
	if !IfFileExists(fileNameA) {
		return Errf("")
	}

	srcStatT, errT := os.Stat(fileNameA)
	if errT != nil {
		return Errf("error os.Stat src %s: %s", fileNameA, errT.Error())
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	outputFileT := outputFileA
	if outputFileT == "" {
		outputFileT = fileNameA + ".txdef"
	}

	fileContenT, errT := ioutil.ReadFile(fileNameA)
	if errT != nil {
		return errT
	}

	writeContentT := EncryptDataByTXDEF(fileContenT, codeT)
	if writeContentT == nil {
		return Errf("encrypt data failed")
	}

	bufT := []byte("//TXDEF#")

	bufT = append(bufT, writeContentT...)

	errT = ioutil.WriteFile(outputFileT, bufT, srcStatT.Mode())
	if errT != nil {
		return errT
	}

	return nil
}

func EncryptFileByTXDEFStream(fileNameA, codeA, outputFileA string) error {
	if !IfFileExists(fileNameA) {
		return Errf("")
	}

	srcStatT, errT := os.Stat(fileNameA)
	if errT != nil {
		return Errf("error os.Stat src %s: %s", fileNameA, errT.Error())
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	outputFileT := outputFileA
	if outputFileT == "" {
		outputFileT = fileNameA + ".txdef"
	}

	fileT, errT := os.Open(fileNameA)
	if errT != nil {
		return Errf("failed to open source file: %v", errT)
	}

	defer fileT.Close()

	file2T, errT := os.OpenFile(outputFileT, os.O_CREATE, srcStatT.Mode())
	if errT != nil {
		return Errf("failed to create target file: %v", errT)
	}

	defer file2T.Close()

	bufT := bufio.NewWriter(file2T)

	errT = EncryptStreamByTXDEF(fileT, codeT, bufT)

	if errT != nil {
		return Errf("failed to encrypt: %v", errT)
	}

	errT = bufT.Flush()

	if errT != nil {
		return Errf("failed to flush output file: %v", errT)
	}

	return nil
}

func DecryptFileByTXDEFStream(fileNameA, codeA, outputFileA string) error {
	if !IfFileExists(fileNameA) {
		return Errf("")
	}

	srcStatT, errT := os.Stat(fileNameA)
	if errT != nil {
		return Errf("error os.Stat src %s: %s", fileNameA, errT.Error())
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	outputFileT := outputFileA
	if outputFileT == "" {
		outputFileT = fileNameA + ".untxdef"
	}

	fileT, errT := os.Open(fileNameA)
	if errT != nil {
		return Errf("failed to open source file: %v", errT)
	}

	defer fileT.Close()

	file2T, errT := os.OpenFile(outputFileT, os.O_CREATE, srcStatT.Mode())
	if errT != nil {
		return Errf("failed to create target file: %v", errT)
	}

	defer file2T.Close()

	bufT := bufio.NewWriter(file2T)

	errT = DecryptStreamByTXDEF(fileT, codeT, bufT)

	if errT != nil {
		return Errf("failed to decrypt: %v", errT)
	}

	errT = bufT.Flush()

	if errT != nil {
		return Errf("failed to flush output file: %v", errT)
	}

	return nil
}

func ErrorToString(errA error) string {
	if errA == nil {
		return ""
	}

	return GenerateErrorString(errA.Error())
}

func EncryptFileByTXDEFS(fileNameA, codeA, outputFileA string) string {
	return ErrorToString(EncryptFileByTXDEF(fileNameA, codeA, outputFileA))
}

func EncryptFileByTXDEFStreamS(fileNameA, codeA, outputFileA string) string {
	return ErrorToString(EncryptFileByTXDEFStream(fileNameA, codeA, outputFileA))
}

func DecryptFileByTXDEF(fileNameA, codeA, outputFileA string) error {
	if !IfFileExists(fileNameA) {
		return Errf("file not exists")
	}

	srcStatT, errT := os.Stat(fileNameA)
	if errT != nil {
		return Errf("error os.Stat src %s: %s", fileNameA, errT.Error())
	}

	codeT := codeA
	if codeT == "" {
		codeT = "topxeq"
	}

	outputFileT := outputFileA
	if outputFileT == "" {
		outputFileT = fileNameA + ".untxdef"
	}

	fileContenT, errT := ioutil.ReadFile(fileNameA)
	if errT != nil {
		return errT
	}

	if bytes.HasPrefix(fileContenT, []byte("//TXDEF#")) {
		fileContenT = fileContenT[8:]
	}

	writeContentT := DecryptDataByTXDEF(fileContenT, codeT)
	if writeContentT == nil {
		return Errf("decrypt data failed")
	}

	errT = ioutil.WriteFile(outputFileT, writeContentT, srcStatT.Mode())
	if errT != nil {
		return errT
	}

	return nil

}

func DecryptFileByTXDEFS(fileNameA, codeA, outputFileA string) string {
	return ErrorToString(DecryptFileByTXDEF(fileNameA, codeA, outputFileA))
}

func DecryptFileByTXDEFStreamS(fileNameA, codeA, outputFileA string) string {
	return ErrorToString(DecryptFileByTXDEFStream(fileNameA, codeA, outputFileA))
}

func Pkcs7Padding(ciphertext []byte, blockSize int) []byte {
	padding := blockSize - len(ciphertext)%blockSize
	padtext := bytes.Repeat([]byte{byte(padding)}, padding)
	//	Pl("padding: %v", padding)
	return append(ciphertext, padtext...)
}

// func Pkcs7Unpad(b []byte, blocksize int) ([]byte, error) {
// 	if blocksize <= 0 {
// 		return nil, Errf("ErrInvalidBlockSize")
// 	}
// 	if b == nil || len(b) == 0 {
// 		return nil, Errf("ErrInvalidPKCS7Data")
// 	}
// 	if len(b)%blocksize != 0 {
// 		return nil, Errf("ErrInvalidPKCS7Padding")
// 	}
// 	c := b[len(b)-1]
// 	n := int(c)
// 	if n == 0 || n > len(b) {
// 		return nil, Errf("ErrInvalidPKCS7Padding")
// 	}
// 	for i := 0; i < n; i++ {
// 		if b[len(b)-n+i] != c {
// 			return nil, Errf("ErrInvalidPKCS7Padding")
// 		}
// 	}
// 	return b[:len(b)-n], nil
// }

func AESEncrypt(src, key []byte) ([]byte, error) {
	//	key = toMD5(key)
	keyT := key
	if len(keyT) > 16 {
		keyT = keyT[0:16]
	}
	block, err := aes.NewCipher(keyT)

	if err != nil {
		return nil, err
	}
	bs := block.BlockSize()
	//	Printf("Src: %v\n", src)
	//	Printf("Key: %v\n", key)
	//	Printf("Block size: %v\n", bs)
	//	src = zeroPadding(src, bs)
	src = Pkcs7Padding(src, bs)
	//	Pl("After padding: %v", src)
	if len(src)%bs != 0 {
		return nil, errors.New("Need a multiple of the blocksize")
	}
	out := make([]byte, len(src))
	dst := out
	iv := []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
	for len(src) > 0 {
		//		Pl("Encing: %v\n", src[:bs])
		for j := 0; j < bs; j++ {
			src[j] ^= iv[j]
		}
		//		Pl("EncingXORed: %v", src[:bs])
		block.Encrypt(dst, src[:bs])
		src = src[bs:]

		for j := 0; j < bs; j++ {
			iv[j] = dst[j]
		}
		dst = dst[bs:]
	}
	return out, nil
}

// func Unpad(src []byte) ([]byte, error) {
// 	length := len(src)
// 	unpadding := int(src[length-1])

// 	if unpadding > length {
// 		return nil, errors.New("unpad error. This could happen when incorrect encryption key is used")
// 	}

// 	return src[:(length - unpadding)], nil
// }

func AESDecrypt(src, key []byte) ([]byte, error) {
	//	key = toMD5(key)
	keyT := key
	if len(keyT) > 16 {
		keyT = keyT[0:16]
	}

	block, err := aes.NewCipher(keyT)

	if err != nil {
		return nil, err
	}

	bs := block.BlockSize()
	//	Printf("Src: %v\n", src)
	//	Printf("Key: %v\n", key)
	// Pl("Block size: %v", bs)
	//	src = zeroPadding(src, bs)
	// beforeLen := len(src)
	// // src = Pkcs7Padding(src, bs)
	// afterLen := len(src)
	// diffLen := afterLen - beforeLen
	// Pl("beforeLen: %v, afterLen: %v, diffLen: %v", beforeLen, afterLen, diffLen)
	//	Pl("After padding: %v", src)
	if len(src)%bs != 0 {
		return nil, errors.New("Need a multiple of the blocksize")
	}

	out := make([]byte, len(src))
	dst := out

	iv := []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

	for len(src) > 0 {
		//		Pl("EncingXORed: %v", src[:bs])
		block.Decrypt(dst, src[:bs])

		//		Pl("Encing: %v\n", src[:bs])
		for j := 0; j < bs; j++ {
			dst[j] ^= iv[j]
		}

		for j := 0; j < bs; j++ {
			iv[j] = src[j]
		}

		src = src[bs:]

		dst = dst[bs:]
	}

	// Pl("out 1: %#v", out)
	outLenT := len(out)
	unpadLenT := int(out[outLenT-1])

	if unpadLenT <= outLenT {
		for i := 0; i < unpadLenT; i++ {
			if out[outLenT-1-i] != byte(unpadLenT) {
				return out, nil
			}
		}

		out = out[:outLenT-unpadLenT]
	}

	// Pl("out len: %v", len(out))
	// out = out[:len(out)-diffLen]
	return out, nil
}

// func AESDecrypt(src, key []byte) ([]byte, error) {
// 	//	key = toMD5(key)
// 	keyT := key
// 	if len(keyT) > 16 {
// 		keyT = keyT[0:16]
// 	}

// 	block, err := aes.NewCipher(keyT)

// 	if err != nil {
// 		return nil, err
// 	}

// 	bs := block.BlockSize()
// 	//	Printf("Src: %v\n", src)
// 	//	Printf("Key: %v\n", key)
// 	//	Printf("Block size: %v\n", bs)
// 	//	src = zeroPadding(src, bs)
// 	beforeLen := len(src)
// 	src = Pkcs7Padding(src, bs)
// 	// src, errT := Pkcs7Unpad(src, bs)
// 	// if errT != nil {
// 	// 	return nil, errT
// 	// }
// 	Pl("src: %#v", src)
// 	afterLen := len(src)

// 	diffLen := afterLen - beforeLen
// 	lenT := len(src)

// 	if lenT < 1 {
// 		return nil, errors.New("Zero length")
// 	}

// 	//	Pl("beforeLen: %v, afterLen: %v, diffLen: %v", beforeLen, afterLen, diffLen)
// 	//	Pl("After padding: %v", src)
// 	if lenT%bs != 0 {
// 		return nil, errors.New("Need a multiple of the blocksize")
// 	}

// 	out := make([]byte, lenT)
// 	dst := out
// 	iv := []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
// 	for lenT > 0 {
// 		//		Pl("EncingXORed: %v", src[:bs])
// 		block.Decrypt(dst, src[:bs])

// 		//		Pl("Encing: %v\n", src[:bs])
// 		for j := 0; j < bs; j++ {
// 			dst[j] ^= iv[j]
// 		}

// 		for j := 0; j < bs; j++ {
// 			iv[j] = src[j]
// 		}

// 		src = src[bs:]

// 		dst = dst[bs:]
// 	}
// 	// diffLen := int(src[lenT-1])
// 	// Pl("diffLen: %v", diffLen)
// 	out = out[:len(out)-diffLen]
// 	// out, errT = Pkcs7Unpad(out, bs)

// 	// if errT != nil {
// 	// 	return nil, errT
// 	// }

// 	return out, nil
// }

// URL相关 url related

func AnalyzeURLParams(strA string) map[string]string {
	rMapT := make(map[string]string)

	tmpL := strings.Split(strA, "__")

	for i := range tmpL {
		tmpL2 := strings.SplitN(tmpL[i], "=", 2)

		if len(tmpL2) < 2 {
			continue
		}

		rMapT[tmpL2[0]] = tmpL2[1]
	}

	return rMapT
}

func UrlEncode(strA string) string {
	return url.QueryEscape(strA)
}

func UrlEncode2(strA string) string {
	u, err := url.Parse(strA)
	if err != nil {
		return GenerateErrorString("parsing URL failed")
	}
	return u.String()
}

func UrlDecode(strA string) string {
	rStrT, errT := url.QueryUnescape(strA)
	if errT != nil {
		return GenerateErrorString(errT.Error())
	}
	return rStrT
}

// JoinURL concat a base URL and a relative URL
func JoinURL(urlBaseA string, urlNextA string) string {
	u, err := url.Parse(urlNextA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}

	base, err := url.Parse(urlBaseA)
	if err != nil {
		return GenerateErrorString(err.Error())
	}
	return base.ResolveReference(u).String()
}

func FormToMap(formA url.Values) map[string]string {
	mapT := make(map[string]string, 0)

	if formA == nil {
		return mapT
	}

	for k, v := range formA {
		mapT[k] = v[0]
	}

	return mapT
}

// debug related

var DebugModeG bool = false
var debugLockG sync.Mutex
var debugBufferG bytes.Buffer

func AddDebug(strA string) {
	if DebugModeG {
		debugLockG.Lock()
		debugBufferG.WriteString(strA + "\n")
		debugLockG.Unlock()
	}
}

func AddDebugF(formatA string, argsA ...interface{}) {
	if !DebugModeG {
		return
	}

	debugLockG.Lock()

	debugBufferG.WriteString(fmt.Sprintf(fmt.Sprintf("[%v] ", GetNowTimeStringFormal())+formatA+"\n", argsA...))

	debugLockG.Unlock()
}

func ClearDebug() {
	debugBufferG.Truncate(0)
}

func GetDebug() string {
	return debugBufferG.String()
}

// http/web service related

func DownloadPageUTF8(urlA string, postDataA url.Values, customHeaders string, timeoutSecsA time.Duration, optsA ...string) string {
	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	var urlT string
	if !StartsWithIgnoreCase(urlA, "http") {
		urlT = "http://" + urlA
	} else {
		urlT = urlA
	}

	var respT *http.Response
	var errT error
	var req *http.Request

	if !IsEmptyTrim(customHeaders) {
		if postDataA == nil {
			req, errT = http.NewRequest("GET", urlT, nil)
		} else {
			req, errT = http.NewRequest("POST", urlT, nil)
			req.PostForm = postDataA
		}

		headersT := SplitLines(customHeaders)

		for i := 0; i < len(headersT); i++ {
			lineT := headersT[i]
			aryT := strings.Split(lineT, ":")
			if len(aryT) < 2 {
				continue
			}
			req.Header.Add(aryT[0], Trim(Replace(aryT[1], "`", ":")))
			//TXPl("%s=%s", aryT[0], aryT[1])
		}

		if IfSwitchExistsWhole(optsA, "-verbose") {
			Pl("REQ: %v", req)
		}

		respT, errT = client.Do(req)
	} else {
		if IfSwitchExistsWhole(optsA, "-verbose") {
			Pl("URL: %v", urlT)
		}

		if postDataA == nil {
			respT, errT = client.Get(urlT)
		} else {
			if IfSwitchExistsWhole(optsA, "-verbose") {
				Pl("POST data: %v", postDataA)
			}

			respT, errT = client.PostForm(urlT, postDataA)
		}
	}

	if errT == nil {
		defer respT.Body.Close()
		if respT.StatusCode != 200 {
			if IfSwitchExistsWhole(optsA, "-detail") {
				Pl("response status: %v (%v)", respT.StatusCode, respT)
			}

			return GenerateErrorStringF("response status: %v", respT.StatusCode)
		} else {
			body, errT := ioutil.ReadAll(respT.Body)

			if errT == nil {
				return string(body)
			} else {
				return GenerateErrorString(errT.Error())
			}
		}
	} else {
		return GenerateErrorString(errT.Error())
	}
}

// DownloadPage download page with any encoding and convert to UTF-8
func DownloadPage(urlA string, originalEncodingA string, postDataA url.Values, customHeaders string, timeoutSecsA time.Duration) string {
	client := &http.Client{
		Timeout: time.Second * timeoutSecsA,
	}

	var urlT string
	if !strings.HasPrefix(strings.ToLower(urlA), "http") {
		urlT = "http://" + urlA
	} else {
		urlT = urlA
	}

	var respT *http.Response
	var errT error
	var req *http.Request

	if Trim(customHeaders) != "" {
		if postDataA == nil {
			req, errT = http.NewRequest("GET", urlT, nil)
		} else {
			req, errT = http.NewRequest("POST", urlT, nil)
			req.PostForm = postDataA
		}

		headersT := SplitLines(customHeaders)

		for i := 0; i < len(headersT); i++ {
			lineT := headersT[i]
			aryT := strings.Split(lineT, ":")
			if len(aryT) < 2 {
				continue
			}
			req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
		}

		respT, errT = client.Do(req)
	} else {
		if postDataA == nil {
			respT, errT = client.Get(urlT)
		} else {
			respT, errT = client.PostForm(urlT, postDataA)
		}
	}

	if errT == nil {
		defer respT.Body.Close()
		if respT.StatusCode != 200 {
			return GenerateErrorStringF("response status: %v", respT.StatusCode)
		} else {
			body, errT := ioutil.ReadAll(respT.Body)

			if errT == nil {
				if (originalEncodingA == "") || (strings.ToLower(originalEncodingA) == "utf-8") {
					return string(body)
				} else {
					return ConvertToUTF8(body, originalEncodingA)
				}
			} else {
				return GenerateErrorString(errT.Error())
			}
		}
	} else {
		return GenerateErrorString(errT.Error())
	}

}

// HttpRequest download page with any encoding and convert to UTF-8
func HttpRequest(urlA string, methodA string, originalEncodingA string, postDataA url.Values, customHeaders string, timeoutSecsA time.Duration, optsA ...string) string {
	client := &http.Client{
		Timeout: time.Second * timeoutSecsA,
	}

	var urlT string
	if !strings.HasPrefix(strings.ToLower(urlA), "http") {
		urlT = "http://" + urlA
	} else {
		urlT = urlA
	}

	var respT *http.Response
	var errT error
	var req *http.Request

	if postDataA == nil {
		req, errT = http.NewRequest(methodA, urlT, nil)
		// req.PostForm = postDataA
	} else {
		req, errT = http.NewRequest(methodA, urlT, strings.NewReader(postDataA.Encode()))
		req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	}

	headersT := SplitLines(customHeaders)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.Split(lineT, ":")
		if len(aryT) < 2 {
			continue
		}
		req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("REQ: %v", req)
	}

	respT, errT = client.Do(req)

	if errT == nil {
		defer respT.Body.Close()

		if IfSwitchExistsWhole(optsA, "-verbose") {
			Pl("response status: %v (%v)", respT.StatusCode, respT)
		}

		if respT.StatusCode != 200 {
			return GenerateErrorStringF("response status: %v", respT.StatusCode)
		} else {
			body, errT := ioutil.ReadAll(respT.Body)

			if errT == nil {
				if (originalEncodingA == "") || (strings.ToLower(originalEncodingA) == "utf-8") {
					return string(body)
				} else {
					return ConvertToUTF8(body, originalEncodingA)
				}
			} else {
				return GenerateErrorString(errT.Error())
			}
		}
	} else {
		return GenerateErrorString(errT.Error())
	}

}

func DownloadPageByMap(urlA string, originalEncodingA string, postDataA map[string]string, customHeaders string, timeoutSecsA time.Duration) string {
	if postDataA == nil {
		return DownloadPage(urlA, originalEncodingA, nil, customHeaders, timeoutSecsA)
	}

	postDataT := url.Values{}

	for k, v := range postDataA {

		postDataT.Set(k, v)

	}

	return DownloadPage(urlA, originalEncodingA, postDataT, customHeaders, timeoutSecsA)
}

func GetLastComponentOfUrl(urlA string) string {
	urlT, errT := url.Parse(urlA)
	if errT != nil {
		return GenerateErrorStringF(errT.Error())
	}

	splitRT := strings.Split(urlT.Path, "/")

	return splitRT[len(splitRT)-1]
}

func DownloadFile(urlA, dirA, fileNameA string, ifRenameA bool) string {

	var urlT string
	var fileNameT string = fileNameA

	if !StartsWithIgnoreCase(urlA, "http://") {
		urlT = "http://" + urlA
	} else {
		urlT = urlA
	}

	respT, errT := http.Get(urlT)
	if errT != nil {
		return GenerateErrorStringF("failed to get URL: %v", errT.Error())
	}

	if respT.StatusCode != 200 {
		return GenerateErrorStringF("failed to get URL: status code = %v", respT.StatusCode)
	}

	defer respT.Body.Close()

	if fileNameT == "" {
		fileNameT = GetLastComponentOfUrl(urlT)
	}

	if dirA != "" {
		fileNameT = filepath.Join(dirA, fileNameT)
	}

	if ifRenameA {
		fileNameT = GetAvailableFileName(fileNameT)
	}

	fileT, errT := os.Create(fileNameT)
	if errT != nil {
		return GenerateErrorStringF("failed to create file: %v", errT.Error())
	}
	defer fileT.Close()

	// if respT.ContentLength == -1 {
	// 	tmpBuf, _ := ioutil.ReadAll(respT.Body)
	// 	return GenerateErrorStringF("failed to get http response content length: %v\n%#v", string(tmpBuf), respT)
	// }

	bufT := make([]byte, 1000000)

	for {
		n, errT := respT.Body.Read(bufT)

		if n == 0 && errT.Error() == "EOF" {
			break
		}

		if (errT != nil) && (errT.Error() != "EOF") {
			return GenerateErrorStringF("failed to download: %v", errT.Error())
		}

		fileT.WriteString(string(bufT[:n]))
	}

	// valid download exe
	// fi, errT := fileT.Stat()
	// if errT == nil {
	// 	if fi.Size() != respT.ContentLength {
	// 		return GenerateErrorStringF("Downloaded file size error")
	// 	}
	// }

	return fileNameT
}

func DownloadBytes(urlA string) ([]byte, error) {

	var urlT string

	if !StartsWithIgnoreCase(urlA, "http://") {
		urlT = "http://" + urlA
	} else {
		urlT = urlA
	}

	respT, errT := http.Get(urlT)
	if errT != nil {
		return nil, Errf("failed to get URL: %v", errT.Error())
	}

	if respT.StatusCode != 200 {
		return nil, Errf("failed to get URL: status code = %v", respT.StatusCode)
	}

	defer respT.Body.Close()

	bufT, errT := ioutil.ReadAll(respT.Body)

	if errT != nil {
		return nil, Errf("failed to get http response body: %v", errT)
	}

	return bufT, nil
}

// PostRequest : another POST request sender
func PostRequest(urlA, reqBodyA string, timeoutSecsA time.Duration) (string, error) {

	req, err := http.NewRequest("POST", urlA, strings.NewReader(reqBodyA))

	if err != nil {
		return "", err
	}

	req.Header.Set("Content-Type", "application/json; encoding=utf-8")

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", err
	}

	defer resp.Body.Close()

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// PostRequestX : Post Request with custom headers
func PostRequestX(urlA, reqBodyA string, customHeadersA string, timeoutSecsA time.Duration, optsA ...string) (string, error) {

	req, err := http.NewRequest("POST", urlA, strings.NewReader(reqBodyA))

	if err != nil {
		return "", err
	}

	headersT := SplitLines(customHeadersA)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.SplitN(lineT, ":", 2)
		if len(aryT) < 2 {
			continue
		}
		req.Header.Add(aryT[0], Replace(aryT[1], "TX_COLONS_XT", ":"))
		// Pl("%s=%s", aryT[0], aryT[1])
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("POST data: %v", reqBodyA)
		Pl("REQ: %v", req)
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", err
	}

	defer resp.Body.Close()

	if IfSwitchExistsWhole(optsA, "-detail") {
		Pl("response status: %v (%v)", resp.StatusCode, resp)
	}

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// PutRequestX : Put Request with custom headers
func PutRequestX(urlA, reqBodyA string, customHeadersA string, timeoutSecsA time.Duration, optsA ...string) (string, error) {

	req, err := http.NewRequest("PUT", urlA, strings.NewReader(reqBodyA))

	if err != nil {
		return "", err
	}

	headersT := SplitLines(customHeadersA)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.Split(lineT, ":")
		if len(aryT) < 2 {
			continue
		}
		req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
		// Pl("%s=%s", aryT[0], aryT[1])
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("PUT data: %v", reqBodyA)
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("REQ: %v", req)
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", err
	}

	defer resp.Body.Close()

	if IfSwitchExistsWhole(optsA, "-detail") {
		Pl("response status: %v (%v)", resp.StatusCode, resp)
	}

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// PostRequestBytesX : PostRequest with custom headers
func PostRequestBytesX(urlA string, reqBodyA []byte, customHeadersA string, timeoutSecsA time.Duration) ([]byte, error) {

	req, err := http.NewRequest("POST", urlA, bytes.NewReader(reqBodyA))

	if err != nil {
		return nil, err
	}

	headersT := SplitLines(customHeadersA)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.Split(lineT, ":")

		if len(aryT) < 2 {
			continue
		}

		req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
		// Pl("%s=%s", aryT[0], aryT[1])
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}

	defer resp.Body.Close()

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}

	return body, nil
}

// RequestX : Network(http) Request with custom headers
func RequestX(urlA, methodA, reqBodyA string, customHeadersA string, timeoutSecsA time.Duration, optsA ...string) (string, error) {

	// methodA: GET, POST, PUT, etc
	req, err := http.NewRequest(methodA, urlA, strings.NewReader(reqBodyA))

	if err != nil {
		return "", err
	}

	headersT := SplitLines(customHeadersA)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.Split(lineT, ":")
		if len(aryT) < 2 {
			continue
		}
		req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
		// Pl("%s=%s", aryT[0], aryT[1])
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("REQUEST data: %v", reqBodyA)
	}

	if IfSwitchExistsWhole(optsA, "-verbose") {
		Pl("REQ: %v", req)
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", err
	}

	defer resp.Body.Close()

	if IfSwitchExistsWhole(optsA, "-detail") {
		Pl("response status: %v (%v)", resp.StatusCode, resp)
	}

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	return string(body), nil
}

// PostRequestBytesX : PostRequest with custom headers
func PostRequestBytesWithMSSHeaderX(urlA string, reqBodyA []byte, customHeadersA map[string]string, timeoutSecsA time.Duration) ([]byte, error) {

	req, err := http.NewRequest("POST", urlA, bytes.NewReader(reqBodyA))

	if err != nil {
		return nil, err
	}

	if customHeadersA != nil {
		for k, v := range customHeadersA {
			req.Header.Add(k, v)
		}
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
	}

	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}

	defer resp.Body.Close()

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}

	return body, nil
}

// PostRequestBytesWithCookieX : PostRequest with custom headers
func PostRequestBytesWithCookieX(urlA string, reqBodyA []byte, customHeadersA string, jarA *cookiejar.Jar, timeoutSecsA time.Duration) ([]byte, *cookiejar.Jar, error) {

	req, err := http.NewRequest("POST", urlA, bytes.NewReader(reqBodyA))

	if err != nil {
		return nil, nil, err
	}

	headersT := SplitLines(customHeadersA)

	for i := 0; i < len(headersT); i++ {
		lineT := headersT[i]
		aryT := strings.Split(lineT, ":")

		if len(aryT) < 2 {
			continue
		}

		req.Header.Add(aryT[0], Replace(aryT[1], "`", ":"))
		// Pl("%s=%s", aryT[0], aryT[1])
	}

	jarT := jarA

	if jarT == nil {
		jarT, _ = cookiejar.New(nil)
	}

	client := &http.Client{
		//CheckRedirect: redirectPolicyFunc,
		Timeout: time.Second * timeoutSecsA,
		Jar:     jarT,
	}

	resp, err := client.Do(req)
	if err != nil {
		return nil, nil, err
	}

	defer resp.Body.Close()

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, nil, err
	}

	// Pl("%#v", client.Jar)

	// cookiesT := resp.Cookies()

	// for i, v := range cookiesT {
	// 	Pl("%v, %#v", i, v)
	// }

	return body, jarT, nil
}

func GetFormValueWithDefaultValue(reqA *http.Request, keyA string, defaultA string) string {
	valueT, ok := reqA.Form[keyA]
	if ok {
		return valueT[0]
	} else {
		return defaultA
	}
}

func GenerateJSONPResponse(statusA string, valueA string, reqA *http.Request, argsA ...string) string {
	_, valueOnlyT := reqA.Form["valueonly"]

	if valueOnlyT {
		if _, withErrorT := reqA.Form["witherror"]; withErrorT {
			if statusA != "success" {
				return GenerateErrorString(valueA)
			}
		}

		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA

		if argsA != nil {
			lenT := len(argsA) / 2

			for i := 0; i < lenT; i++ {
				mT[argsA[i*2]] = argsA[i*2+1]
			}
		}

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GenerateJSONPResponseMix(statusA string, valueA string, reqA *http.Request, mapA map[string]string) string {
	_, valueOnlyT := reqA.Form["valueonly"]

	if valueOnlyT {
		if _, withErrorT := reqA.Form["witherror"]; withErrorT {
			if statusA != "success" {
				return GenerateErrorString(valueA)
			}
		}

		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA

		if mapA != nil {
			for k, v := range mapA {
				mT[k] = v
			}
		}

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GenerateJSONPResponseWithMore(statusA string, valueA string, reqA *http.Request, argsA ...string) string {
	_, valueOnlyT := reqA.Form["valueonly"]

	if valueOnlyT {
		if _, withErrorT := reqA.Form["witherror"]; withErrorT {
			if statusA != "success" {
				return GenerateErrorString(valueA)
			}
		}

		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA

		if argsA != nil && len(argsA) > 0 {
			lenT := len(argsA) / 2

			for i := 0; i < lenT; i++ {
				mT[argsA[i*2]] = argsA[i*2+1]
			}
		}

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GenerateJSONPResponseWithObject(statusA string, valueA string, objectA string, reqA *http.Request) string {
	_, valueOnlyT := reqA.Form["valueonly"]
	_, objectOnlyT := reqA.Form["objectonly"]

	if objectOnlyT {
		return objectA
	} else if valueOnlyT {
		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA
		mT["Object"] = objectA

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GenerateJSONPResponseWith2Object(statusA string, valueA string, objectA string, object2A string, reqA *http.Request) string {
	_, valueOnlyT := reqA.Form["valueonly"]
	_, objectOnlyT := reqA.Form["objectonly"]

	if objectOnlyT {
		return objectA
	} else if valueOnlyT {
		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA
		mT["Object"] = objectA
		mT["Object2"] = object2A

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GenerateJSONPResponseWith3Object(statusA string, valueA string, objectA string, object2A string, object3A string, reqA *http.Request) string {
	_, valueOnlyT := reqA.Form["valueonly"]
	_, objectOnlyT := reqA.Form["objectonly"]

	if objectOnlyT {
		return objectA
	} else if valueOnlyT {
		return valueA
	} else {
		mT := make(map[string]string)
		mT["Status"] = statusA
		mT["Value"] = valueA
		mT["Object"] = objectA
		mT["Object2"] = object2A
		mT["Object3"] = object3A

		returnValue, ifReturnValue := reqA.Form["returnvalue"]

		if ifReturnValue {
			mT["ReturnValue"] = returnValue[0]
		}

		name, ok := reqA.Form["callback"]
		if ok {
			if valueOnlyT {
				return fmt.Sprintf("%v(%v);", name[0], valueA)
			} else {
				return fmt.Sprintf("%v(%v);", name[0], ObjectToJSON(mT))
			}
		}

		return fmt.Sprintf("%v", ObjectToJSON(mT))
	}
}

func GetSuccessValue(strA string) string {
	rv := JSONToMapStringString(strA)
	if rv == nil {
		return GenerateErrorString("invalid json data")
	}

	statusT, ok := rv["Status"]
	if !ok {
		return GenerateErrorString("invalid json data")
	}

	if statusT != "success" {
		return GenerateErrorString("status not success")
	}

	valueT, ok := rv["Value"]
	if !ok {
		return GenerateErrorString("invalid json data")
	}

	return valueT
}

// 数学相关 math related

func LimitPrecision(nA interface{}, digitA int) error {
	switch t := nA.(type) {
	case *float64:
		vT := *(nA.(*float64))
		*(nA.(*float64)) = math.Round(vT*math.Pow10(digitA)) / math.Pow10(digitA)
	case *[]float64:
		pT := (nA.(*[]float64))

		lenT := len(*pT)

		for i := 0; i < lenT; i++ {
			(*pT)[i] = math.Round((*pT)[i]*math.Pow10(digitA)) / math.Pow10(digitA)
		}

	default:
		return Errf("%v", "unknown type: %v", t)
	}

	return nil

}

func Float32ArrayToFloat64Array(aryA []float32) []float64 {
	if aryA == nil {
		return nil
	}

	rs := make([]float64, len(aryA))

	for i := 0; i < len(aryA); i++ {
		rs[i] = float64(aryA[i])
	}

	return rs
}

func GenerateRandomFloats(sizeA int) []float64 {
	bufT := make([]float64, sizeA)

	Randomize()

	for i := 0; i < sizeA; i++ {
		bufT[i] = rand.Float64()
	}

	return bufT
}

func CalCosineSimilarityBetweenFloatsBig(f1, f2 []float64) float64 {
	if f1 == nil || f2 == nil {
		return -1
	}

	l1 := len(f1)
	l2 := len(f2)

	if l1 != l2 {
		return -1
	}

	var rr *big.Float = new(big.Float)
	var f1r *big.Float = new(big.Float)
	var f2r *big.Float = new(big.Float)

	for i := 0; i < l1; i++ {
		f1b := new(big.Float).SetFloat64(f1[i])
		f2b := new(big.Float).SetFloat64(f2[i])
		rr.Add(rr, new(big.Float).Mul(f1b, f2b))
		f1r.Add(f1r, new(big.Float).Mul(f1b, f1b))
		f2r.Add(f2r, new(big.Float).Mul(f2b, f2b))
	}

	tmprs1 := f1r.Sqrt(f1r)
	tmprs2 := f2r.Sqrt(f2r)

	tmprsr := new(big.Float).Mul(tmprs1, tmprs2)

	rs, _ := (rr.Quo(rr, tmprsr)).Float64()

	return rs
}

// 数据库相关 database related

// GetDBConnection must close it manually
func GetDBConnection(driverA string, pathT string) *sql.DB {
	dbT, errT := sql.Open(driverA, pathT)

	if errT != nil {
		return nil
	}

	errT = dbT.Ping()

	if errT != nil {
		dbT.Close()
		return nil
	}

	return dbT
}

// GetDBRowCount 获取类似select count(*)的结果
func GetDBRowCount(dbA *sql.DB, sqlA string) (int, error) {
	if dbA == nil {
		return 0, fmt.Errorf("DB pointer nil")
	}

	var c int

	errT := dbA.QueryRow(sqlA).Scan(&c)

	if errT == sql.ErrNoRows {
		return 0, fmt.Errorf("no rows")
	}

	return c, nil
}

// GetDBRowCountCompact 获取类似select count(*)的结果
// return < 0 if fail
func GetDBRowCountCompact(dbA *sql.DB, sqlA string) int {
	c, errT := GetDBRowCount(dbA, sqlA)

	if errT != nil {
		return -1
	}

	return c
}

// GetDBResultString 获取类似select a from ...的结果
func GetDBResultString(dbA *sql.DB, sqlA string) (string, error) {
	if dbA == nil {
		return "", fmt.Errorf("DB pointer nil")
	}

	var s string

	errT := dbA.QueryRow(sqlA).Scan(&s)

	if errT == sql.ErrNoRows {
		return "", fmt.Errorf("no rows")
	}

	return s, nil
}

// GetDBResultArray 获取类似select a from ...的多行结果
func GetDBResultArray(dbA *sql.DB, sqlA string) ([][]string, error) {
	if dbA == nil {
		return nil, fmt.Errorf("DB pointer nil")
	}

	rowsT, errT := dbA.Query(sqlA)
	if errT != nil {
		return nil, errT
	}

	defer rowsT.Close()

	columnsT, errT := rowsT.Columns()

	if errT != nil {
		return nil, errT
	}

	// columnsTypesT, errT := rowsT.ColumnTypes()

	columnCountT := len(columnsT)

	if columnCountT < 1 {
		return nil, Errf("zero columns")
	}

	sliceT := make([][]string, 0)

	for rowsT.Next() {
		subSliceT := make([]interface{}, columnCountT)
		subSlicePointerT := make([]interface{}, columnCountT)

		for j := 0; j < columnCountT; j++ {
			subSlicePointerT[j] = &subSliceT[j]
		}

		errT := rowsT.Scan(subSlicePointerT...)

		if errT != nil {
			return nil, errT
		}

		// subSliceT[j] = tmps

		errT = rowsT.Err()
		if errT != nil {
			return nil, errT
		}

		subStringSliceT := make([]string, columnCountT)

		for j := 0; j < columnCountT; j++ {
			subStringSliceT[j] = Spr("%v", subSliceT[j])
		}

		sliceT = append(sliceT, subStringSliceT)

	}

	return sliceT, nil
}

// 文本编码相关 encoding related

// ConvertToGB18030 转换UTF-8字符串为GB18030编码
func ConvertToGB18030(srcA string) string {
	encoderT := mahonia.NewEncoder("GB18030")

	return encoderT.ConvertString(srcA)
	// dst := make([]byte, len(srcA)*2)
	// transformer := simplifiedchinese.GB18030.NewEncoder()
	// nDst, _, err := transformer.Transform(dst, []byte(srcA), true)
	// if err != nil {
	// 	return GenerateErrorStringF("encoding failed")
	// }
	// return string(dst[:nDst])
}

// ConvertToGB18030Bytes 转换UTF-8字符串为GB18030编码的字节切片
// func ConvertToGB18030Bytes(srcA string) []byte {
// 	dst := make([]byte, len(srcA)*2)

// 	transformer := simplifiedchinese.GB18030.NewEncoder()

// 	nDst, _, err := transformer.Transform(dst, []byte(srcA), true)

// 	if err != nil {
// 		return nil
// 	}

// 	return dst[:nDst]
// }
func ConvertToGB18030Bytes(srcA string) []byte {

	encoderT := mahonia.NewEncoder("GB18030")

	tmps := encoderT.ConvertString(srcA)

	// destT := []byte(tmps)

	return []byte(tmps)
}

// func ConvertToUTF8(srcA []byte, srcEncA string) string {
// 	srcEncT := srcEncA

// 	switch srcEncT {
// 	case "", "GB18030", "gb18030", "GBK", "gbk", "GB2312", "gb2312":
// 		dst := make([]byte, len(srcA)*2)
// 		transformer := simplifiedchinese.GB18030.NewDecoder()
// 		nDst, _, err := transformer.Transform(dst, srcA, true)
// 		if err != nil {
// 			return GenerateErrorStringF("encoding failed: %v", err.Error())
// 		}
// 		return string(dst[:nDst])
// 	case "utf-8", "UTF-8":
// 		return string(srcA)
// 	case "windows-1252", "windows1252":
// 		dst := make([]byte, len(srcA)*2)
// 		transformer := charmap.Windows1252.NewDecoder()
// 		nDst, _, err := transformer.Transform(dst, srcA, true)
// 		if err != nil {
// 			return GenerateErrorStringF("encoding failed: %v", srcEncA)
// 		}
// 		return string(dst[:nDst])
// 	default:
// 		return GenerateErrorStringF("unknown encoding: %v", srcEncA)
// 	}
// }
// ConvertToUTF8 转换GB18030编码等字符串(字节形式)为UTF-8字符串
func ConvertToUTF8(srcA []byte, srcEncA string) string {
	srcEncT := srcEncA

	if srcEncT == "" {
		srcEncT = "GB18030"
	}

	decodeT := mahonia.NewDecoder(srcEncT)

	_, cdataT, errT := decodeT.Translate(srcA, true)

	if errT != nil {
		return GenerateErrorStringF("encoding failed: %v", errT.Error())
	}

	return string(cdataT)

}

// ConvertStringToUTF8 转换GB18030编码等字符串为UTF-8字符串
func ConvertStringToUTF8(srcA string, srcEncA string) string {
	srcEncT := srcEncA

	if srcEncT == "" {
		srcEncT = "GB18030"
	}

	decodeT := mahonia.NewDecoder(srcEncT)

	return decodeT.ConvertString(srcA)

}

// XML related

func ReshapeXML(xmlA string) string {
	var errT error

	treeT := etree.NewDocument()

	if treeT == nil {
		return GenerateErrorStringF("create XML tree failed")
	}

	errT = treeT.ReadFromString(xmlA)

	if errT != nil {
		return GenerateErrorStringF("invalid XML: %v", errT)
	}

	treeT.Indent(2)

	outputT, errT := treeT.WriteToString()

	if errT != nil {
		return GenerateErrorStringF("failed to reshape XML: %v", errT)
	}

	return outputT

}

func FlattenXML(xmlA string, nodeA string) string {
	var errT error

	treeT := etree.NewDocument()

	if treeT == nil {
		return GenerateErrorStringF("create XML tree failed")
	}

	errT = treeT.ReadFromString(xmlA)

	if errT != nil {
		return GenerateErrorStringF("invalid XML: %v", errT)
	}

	rootNodeT := treeT.FindElement("//" + nodeA)

	if rootNodeT == nil {
		return GenerateErrorStringF("node not found: %v", nodeA)
	}

	nodesT := rootNodeT.ChildElements()

	var bufT strings.Builder

	for i, v := range nodesT {
		if i > 0 {
			bufT.WriteString("\n")
		}

		bufT.WriteString(Spr("%v: %v", v.Tag, v.Text()))
	}

	return bufT.String()

}

func GetMSSFromXML(xmlA string, nodeA string) (map[string]string, error) {
	var errT error

	treeT := etree.NewDocument()

	if treeT == nil {
		return nil, Errf("create XML tree failed")
	}

	errT = treeT.ReadFromString(xmlA)

	if errT != nil {
		return nil, Errf("invalid XML: %v", errT)
	}

	rootNodeT := treeT.FindElement("//" + nodeA)

	if rootNodeT == nil {
		return nil, Errf("node not found: %v", nodeA)
	}

	nodesT := rootNodeT.ChildElements()

	mapT := make(map[string]string, len(nodesT))
	for _, jv := range nodesT {
		mapT[jv.Tag] = jv.Text()
	}

	return mapT, nil
}

func GetNodeStringFromXML(xmlA string, nodeA string) (string, error) {
	var errT error

	treeT := etree.NewDocument()

	if treeT == nil {
		return "", Errf("create XML tree failed")
	}

	errT = treeT.ReadFromString(xmlA)

	if errT != nil {
		return "", Errf("invalid XML: %v", errT)
	}

	stringNodeT := treeT.FindElement("//" + nodeA)

	if stringNodeT == nil {
		return "", Errf("node not found: %v", nodeA)
	}

	// Pl("xmlnode: %v, %v", stringNodeT, stringNodeT.FullTag())

	return stringNodeT.Text(), nil
}

func GetMSSArrayFromXML(xmlA string, nodeA string) ([]map[string]string, error) {
	var errT error

	treeT := etree.NewDocument()

	if treeT == nil {
		return nil, Errf("create XML tree failed")
	}

	errT = treeT.ReadFromString(xmlA)

	if errT != nil {
		return nil, Errf("invalid XML: %v", errT)
	}

	rootNodeT := treeT.FindElement("//" + nodeA)

	if rootNodeT == nil {
		return nil, Errf("node not found: %v", nodeA)
	}

	nodesT := rootNodeT.ChildElements()

	aryT := make([]map[string]string, 0)

	for _, v := range nodesT {
		internalNodesT := v.ChildElements()

		mapT := make(map[string]string, len(internalNodesT))
		for _, jv := range internalNodesT {
			mapT[jv.Tag] = jv.Text()
		}

		aryT = append(aryT, mapT)
	}

	return aryT, nil
}

// GetXMLNode if no labelsA, return the root node, else return the specific node
// example: tk.GetXMLNode("... XML content", "envelop", "body", "anode")
func GetXMLNode(xmlA string, labelsA ...string) (*xmlx.Node, error) {
	return xmlx.GetXMLNode(xmlA, labelsA...)
}

// // decode xml to map[string]interface{}

// const (
// 	attrPrefix = "@"
// 	textPrefix = "#text"
// )

// var (
// 	//ErrInvalidDocument invalid document err
// 	ErrInvalidDocument = errors.New("invalid document")

// 	//ErrInvalidRoot data at the root level is invalid err
// 	ErrInvalidRoot = errors.New("data at the root level is invalid")
// )

// type node struct {
// 	Parent  *node
// 	Value   map[string]interface{}
// 	Attrs   []xml.Attr
// 	Label   string
// 	Text    string
// 	HasMany bool
// }

// // Decoder instance
// type XMLDecoder struct {
// 	r          io.Reader
// 	attrPrefix string
// 	textPrefix string
// }

// // NewXMLDecoder create new decoder instance
// func NewXMLDecoder(reader io.Reader) *XMLDecoder {
// 	return NewXMLDecoderWithPrefix(reader, attrPrefix, textPrefix)
// }

// // NewXMLDecoderWithPrefix create new decoder instance with custom attribute prefix and text prefix
// func NewXMLDecoderWithPrefix(reader io.Reader, attrPrefix, textPrefix string) *XMLDecoder {
// 	return &XMLDecoder{r: reader, attrPrefix: attrPrefix, textPrefix: textPrefix}
// }

// //Decode xml string to map[string]interface{}
// func (d *XMLDecoder) Decode() (map[string]interface{}, error) {
// 	decoder := xml.NewDecoder(d.r)
// 	n := &node{}
// 	stack := make([]*node, 0)

// 	for {
// 		token, err := decoder.Token()
// 		if err != nil && err != io.EOF {
// 			return nil, err
// 		}

// 		if token == nil {
// 			break
// 		}

// 		switch tok := token.(type) {
// 		case xml.StartElement:
// 			{
// 				n = &node{
// 					Label:  tok.Name.Local,
// 					Parent: n,
// 					Value:  map[string]interface{}{tok.Name.Local: map[string]interface{}{}},
// 					Attrs:  tok.Attr,
// 				}

// 				setAttrs(n, &tok, d.attrPrefix)
// 				stack = append(stack, n)

// 				if n.Parent != nil {
// 					n.Parent.HasMany = true
// 				}

// 				Pl("node add: %#v", stack[len(stack)-1])

// 			}

// 		case xml.CharData:
// 			Pl("CharData: %#v", string(token.(xml.CharData)))
// 			data := strings.TrimSpace(string(tok))
// 			if len(stack) > 0 {
// 				stack[len(stack)-1].Text = data
// 				Pl("insert")
// 			} else if len(data) > 0 {
// 				Pl("insert return")
// 				return nil, ErrInvalidRoot
// 			}
// 			Pl("insert not")

// 		case xml.EndElement:
// 			{
// 				length := len(stack)
// 				stack, n = stack[:length-1], stack[length-1]

// 				if !n.HasMany {
// 					if len(n.Attrs) > 0 {
// 						m := n.Value[n.Label].(map[string]interface{})
// 						m[d.textPrefix] = n.Text
// 					} else {
// 						n.Value[n.Label] = n.Text
// 						Pl("n.Value: %v, n.Label: %v, n.Text: %v", n.Value, n.Label, n.Text)
// 					}
// 				}

// 				if len(stack) == 0 {
// 					return n.Value, nil
// 				}

// 				setNodeValue(n)
// 				n = n.Parent

// 				Pl("n = n.Parent")
// 			}
// 		case xml.ProcInst:
// 			{
// 				tt := token.(xml.ProcInst)
// 				Pl("tt: %v", string(tt.Inst))
// 			}
// 		default:
// 			Pl("token: %#v, tok: %#v", token, tok)
// 		}

// 	}

// 	return nil, ErrInvalidDocument
// }

// func setAttrs(n *node, tok *xml.StartElement, attrPrefix string) {
// 	if len(tok.Attr) > 0 {
// 		m := make(map[string]interface{})
// 		for _, attr := range tok.Attr {
// 			if len(attr.Name.Space) > 0 {
// 				m[attrPrefix+attr.Name.Space+":"+attr.Name.Local] = attr.Value
// 			} else {
// 				m[attrPrefix+attr.Name.Local] = attr.Value
// 			}
// 		}
// 		n.Value[tok.Name.Local] = m
// 	}
// }

// func setNodeValue(n *node) {
// 	if v, ok := n.Parent.Value[n.Parent.Label]; ok {
// 		m := v.(map[string]interface{})
// 		if v, ok = m[n.Label]; ok {
// 			switch item := v.(type) {
// 			case string:
// 				Pl("string item: %v, v: %#v", item, v)
// 				m[n.Label] = []string{item, n.Value[n.Label].(string)}
// 			case []string:
// 				m[n.Label] = append(item, n.Value[n.Label].(string))
// 			case map[string]interface{}:
// 				Pl("map[string]interface{} item: %v, v: %#v", item, v)
// 				vm := getMap(n)
// 				if vm != nil {
// 					m[n.Label] = []map[string]interface{}{item, vm}
// 				}
// 			case []map[string]interface{}:
// 				Pl("[]map[string]interface{} item: %v, v: %#v", item, v)
// 				vm := getMap(n)
// 				if vm != nil {
// 					m[n.Label] = append(item, vm)
// 				}
// 			default:
// 				Pl("item: %v, v: %#v", item, v)
// 			}
// 		} else {
// 			m[n.Label] = n.Value[n.Label]
// 		}

// 	} else {
// 		n.Parent.Value[n.Parent.Label] = n.Value[n.Label]
// 	}
// }

// func getMap(node *node) map[string]interface{} {
// 	if v, ok := node.Value[node.Label]; ok {
// 		switch v.(type) {
// 		case string:
// 			return map[string]interface{}{node.Label: v}
// 		case map[string]interface{}:
// 			return node.Value[node.Label].(map[string]interface{})
// 		}
// 	}

// 	return nil
// }

func FromXML(xmlA string) (interface{}, error) {
	return GetXMLNode(xmlA)
	// decoder := NewXMLDecoder(strings.NewReader(xmlA))
	// result, err := decoder.Decode()

	// if err != nil {
	// 	return nil, err
	// }

	// return result, nil
}

// func FromXML(xmlA string) (map[string]interface{}, error) {
// 	result := make(map[string]interface{})

// 	err := xml.Unmarshal([]byte(xmlA), &result)

// 	if err != nil {
// 		return nil, err
// 	}

// 	return result, nil
// }

func FromXMLWithDefault(xmlA string, defaultA interface{}) interface{} {
	// decoder := NewXMLDecoder(strings.NewReader(xmlA))
	// result, err := decoder.Decode()

	// if err != nil {
	// 	return defaultA
	// }

	// return result

	result, err := GetXMLNode(xmlA)

	if err != nil {
		return defaultA
	}

	return result
}

// 事件相关 event related

// SimpleEvent 简捷的事件结构
type SimpleEvent struct {
	Type  string
	Value string
}

// Init 为SimpleEvent初始化数据
func (p *SimpleEvent) Init(typeA string, valueA string) {
	p.Type = typeA
	p.Value = valueA
}

// CreateSimpleEvent 创建一个SimpleEvent对象，并为其赋初值
func CreateSimpleEvent(typeA string, valueA string) *SimpleEvent {
	p := &SimpleEvent{}

	p.Type = typeA
	p.Value = valueA

	return p
}

// HTML related

func RemoveHtmlTags(strA string) string {
	reT := regexp.MustCompile("<[^>].*?>")
	rStrT := reT.ReplaceAllString(strA, "")

	rStrT = Replace(rStrT, "\r\n", "\n")
	reT2 := regexp.MustCompile("^\\s*?$")
	rStrT2 := reT2.ReplaceAllString(rStrT, "")
	rStrT2 = Replace(rStrT2, "\n\n", "\n")

	return rStrT2
}

func RemoveHtmlTagsX(strA string, optionsA ...string) string {
	if Trim(strA) == "" {
		return strA
	}

	rStrT := RegReplace(strA, "<script[^>]*?>[\\S\\s]*?</script>", "")

	rStrT = RegReplace(rStrT, "<[^>]*?>", "")

	rStrT = strings.Replace(rStrT, "&nbsp;", " ", -1)
	rStrT = strings.Replace(rStrT, "&middot;", "·", -1)
	rStrT = Trim(rStrT)

	if IfSwitchExistsWhole(optionsA, "-removeWhiteSpace") {
		rStrT = strings.Replace(rStrT, "\r", "", -1)
		rStrT = strings.Replace(rStrT, "\n", "", -1)
		rStrT = RegReplace(rStrT, "\\s+", " ")
	}

	if IfSwitchExistsWhole(optionsA, "-replaceComma") {
		rStrT = strings.Replace(rStrT, ",", "`", -1)
	}

	return rStrT
}

func HTMLToText(htmlA string, optionsA ...string) (result string) {
	defer func() {
		r := recover()
		if r != nil {
			result = htmlA
			return
		}
	}()

	if Trim(htmlA) == "" {
		result = ""
		return
	}

	typeT := GetSwitchWithDefaultValue(optionsA, "-type=", "")

	if typeT == "tx" {
		rs := RegReplace(htmlA, "(?i:[\\S\\s]*?<body[^>]*?>([\\s\\S]*?)</body>[\\S\\s]*)", "$1")
		rs = RegReplace(rs, "(?i:<script[^>]*?>[\\s\\S]*?</script>)", "")
		for RegContains(rs, "<[^>]*?>([\\s\\S]*?)</[^>]*?>") {
			rs = RegReplace(rs, "<[^>]*?>([\\s\\S]*?)</[^>]*?>", "$1")
		}
		result = RegReplace(rs, "<[^>]*?>", "")
		return
	}

	docT, errT := html.Parse(strings.NewReader(htmlA))
	if errT != nil {
		result = htmlA
		return
	} else {
		_, textT, simplified, flattened, cleaned, errT := sandblast.ExtractEx(docT, sandblast.KeepLinks)
		if errT != nil {
			result = htmlA
			return
		} else {
			switch typeT {
			case "", "text":
				result = textT
				return
			case "simple", "s":
				result = simplified.DebugString()
				return
			case "flatten", "f":
				result = flattened.DebugString()
				return
			case "cleaned", "c":
				result = cleaned.DebugString()
				return
			case "beautified", "b":
				result = RemoveHtmlTags(cleaned.DebugString())
				return
			case "x":
				reT := regexp.MustCompile("<[^>]*?>\\[\\d*?\\]")
				var tmpRT string
				if flattened == nil {
					tmpRT = reT.ReplaceAllString(textT, "")
				} else {
					tmpRT = reT.ReplaceAllString(flattened.DebugString(), "")
				}
				reT = regexp.MustCompile("<[^>]*?>\\[(.*?)\\([^)]*?\\)\\]")
				tmpRT = reT.ReplaceAllString(tmpRT, "$1")
				reT = regexp.MustCompile("^\\s*?(\\S)")
				tmpRT = reT.ReplaceAllString(tmpRT, "$1")
				result = tmpRT
				return
			default:
				result = textT
				return
			}
		}
	}
}

// Misc Related

func Pass() {

}

func IsNil(v interface{}) bool {
	if v == nil {
		return true
	}

	tmps := fmt.Sprintf("%v", v)

	if tmps == "<nil>" {
		return true
	}

	return false
}

func IsNilOrEmpty(v interface{}) bool {
	if v == nil {
		return true
	}

	switch v.(type) {
	case nil:
		return true
	case string:
		if v.(string) == "" {
			return true
		}
	case []string:
		if len(v.([]string)) < 1 {
			return true
		}
	default:
		tmps := fmt.Sprintf("%v", v)

		if tmps == "<nil>" {
			return true
		}

	}

	return false
}

func IsError(vA interface{}) bool {
	_, ok := vA.(error)
	if ok {
		return true
	}

	return false
}

func TableToMSSJSON(tableA [][]string) string {
	lenT := len(tableA)

	if lenT < 2 {
		return ErrStrf("no data")
	}

	inLenT := len(tableA[0])

	bufT := make([]map[string]string, 0, lenT)

	for i, v := range tableA {
		if i == 0 {
			continue
		}

		inBufT := make(map[string]string, inLenT)

		for j, jv := range v {
			inBufT[tableA[0][j]] = jv
		}

		bufT = append(bufT, inBufT)
	}

	return tk.ToJSONX(bufT, "-default=", "-sort")

}

func GetUUID1() string {
	uuidT, errT := uuid.NewV1()
	if errT != nil {
		return GenerateErrorStringF("failed to generate UUID: %v", errT)
	}

	return uuidT.String()
}

func GetUUID4() string {
	u1 := uuid.Must(uuid.NewV4())
	return u1.String()
}

func GetUUID() string {
	uuidT, errT := uuid.NewV1()
	if errT != nil {
		return GenerateErrorStringF("failed to generate UUID: %v", errT)
	}

	return uuidT.String()
}

func IsFloat64NearlyEqual(a, b float64) bool {

	if math.Abs(a-b) < 0.000001 {
		return true
	}

	return false
}

// SetValue set a value to a pointer
func SetValue(p interface{}, v interface{}) {
	// tk.Pl("%#v", reflect.TypeOf(p).Kind())
	// p = v

	srcRef := reflect.ValueOf(v)
	vp := reflect.ValueOf(p)
	vp.Elem().Set(srcRef)
}

// GetValue get a value from a pointer
func GetValue(p interface{}) interface{} {
	vp := reflect.Indirect(reflect.ValueOf(p))
	return vp.Interface()
}

func GetVar(nameA string) interface{} {
	varMutexG.Lock()
	rs, ok := variableG[nameA]
	varMutexG.Unlock()

	if !ok {
		GenerateErrorString("no key")
	}
	return rs
}

func SetVar(nameA string, valueA interface{}) {
	varMutexG.Lock()
	variableG[nameA] = valueA
	varMutexG.Unlock()
}

func GetFileVar(fileNameA string) interface{} {
	var rs interface{}
	fileVarMutexG.Lock()
	errT := LoadJSONFromFile(fileNameA, &rs)
	fileVarMutexG.Unlock()

	if errT != nil {
		return errT
	}

	return rs
}

func SetFileVar(fileNameA string, valueA interface{}) error {
	fileVarMutexG.Lock()
	errT := SaveJSONIndentToFile(valueA, fileNameA)
	fileVarMutexG.Unlock()

	return errT
}

func CheckErrorFunc(errA error, funcA func()) {
	if errA != nil {
		PlErr(errA)

		if funcA != nil {
			funcA()
		}

		os.Exit(1)
	}

}

func CheckError(errA error, funcsA ...(func())) {
	if errA != nil {
		PlErr(errA)

		if funcsA != nil {
			for _, v := range funcsA {
				v()
			}
		}

		os.Exit(1)
	}

}

func CheckErrorString(strA string, funcsA ...(func())) {
	if IsErrorString(strA) {
		PlErrString(strA)

		if funcsA != nil {
			for _, v := range funcsA {
				v()
			}
		}

		os.Exit(1)
	}

}

func TypeOfValue(vA interface{}) string {
	return fmt.Sprintf("%T", vA)
}

func TypeOfValueReflect(vA interface{}) string {
	rs := reflect.TypeOf(vA)
	return rs.String()
}

func KindOfValueReflect(vA interface{}) string {
	rs := reflect.TypeOf(vA)
	return rs.Kind().String()
}

func GetClipText() string {
	textT, errT := clipboard.ReadAll()
	if errT != nil {
		return GenerateErrorStringF("could not get text from clipboard: %v", errT.Error())
	}

	return textT
}

func GetClipboardTextWithDefault(defaultA string) string {
	textT, errT := clipboard.ReadAll()
	if errT != nil {
		return defaultA
	} else {
		return textT
	}

}

func GetClipboardTextDefaultEmpty() string {
	textT, errT := clipboard.ReadAll()
	if errT != nil {
		return ""
	} else {
		return textT
	}

}

func SetClipText(textA string) {
	clipboard.WriteAll(textA)
}

func GetTextFromFileOrClipboard(fileT string, defaultA string) string {
	if IsEmptyTrim(fileT) {
		return GetClipboardTextWithDefault(defaultA)
	}

	if !IfFileExists(fileT) {
		return GetClipboardTextWithDefault(defaultA)
	}

	return LoadStringFromFileWithDefault(fileT, defaultA)
}

// RemoveItemsInArray
func RemoveItemsInArray(aryA interface{}, startA int, endA int) interface{} {

	aryT, ok := aryA.([]interface{})

	if ok {
		if startA < 0 || startA >= len(aryT) {
			// Pl("Runtime error: %v", "index out of range")
			return nil
		}

		if endA < 0 || endA >= len(aryT) {
			// Pl("Runtime error: %v", "index out of range")
			return nil
		}

		rs := make([]interface{}, 0, len(aryT)-(endA+1-startA))

		rs = append(rs, aryT[:startA]...)
		rs = append(rs, aryT[endA+1:]...)

		return rs
	}

	aryST, ok := aryA.([]string)

	if ok {
		if startA < 0 || startA >= len(aryST) {
			return nil
		}

		if endA < 0 || endA >= len(aryST) {
			return nil
		}

		rs := make([]string, 0, len(aryST)-(endA+1-startA))

		rs = append(rs, aryST[:startA]...)
		rs = append(rs, aryST[endA+1:]...)

		return rs
	}

	aryIT, ok := aryA.([]int)

	if ok {
		if startA < 0 || startA >= len(aryIT) {
			return nil
		}

		if endA < 0 || endA >= len(aryIT) {
			return nil
		}

		rs := make([]int, 0, len(aryIT)-(endA+1-startA))

		rs = append(rs, aryIT[:startA]...)
		rs = append(rs, aryIT[endA+1:]...)

		return rs
	}

	aryI64T, ok := aryA.([]int64)

	if ok {
		if startA < 0 || startA >= len(aryI64T) {
			return nil
		}

		if endA < 0 || endA >= len(aryI64T) {
			return nil
		}

		rs := make([]int64, 0, len(aryI64T)-(endA+1-startA))

		rs = append(rs, aryI64T[:startA]...)
		rs = append(rs, aryI64T[endA+1:]...)

		return rs
	}

	aryFT, ok := aryA.([]float64)

	if ok {
		if startA < 0 || startA >= len(aryFT) {
			return nil
		}

		if endA < 0 || endA >= len(aryFT) {
			return nil
		}

		rs := make([]float64, 0, len(aryFT)-(endA+1-startA))

		rs = append(rs, aryFT[:startA]...)
		rs = append(rs, aryFT[endA+1:]...)

		return rs
	}

	aryBT, ok := aryA.([]bool)

	if ok {
		if startA < 0 || startA >= len(aryBT) {
			return nil
		}

		if endA < 0 || endA >= len(aryBT) {
			return nil
		}

		rs := make([]bool, 0, len(aryBT)-(endA+1-startA))

		rs = append(rs, aryBT[:startA]...)
		rs = append(rs, aryBT[endA+1:]...)

		return rs
	}

	aryByT, ok := aryA.([]byte)

	if ok {
		if startA < 0 || startA >= len(aryByT) {
			return nil
		}

		if endA < 0 || endA >= len(aryByT) {
			return nil
		}

		rs := make([]byte, 0, len(aryByT)-(endA+1-startA))

		rs = append(rs, aryByT[:startA]...)
		rs = append(rs, aryByT[endA+1:]...)

		return rs
	}

	return nil
	// if idxT == 0 {
	// 	return ayrA[idxT + 1:]
	// }

	// if idxT == len(aryA) - 1 {
	// 	return ayrA[0:len(aryA) - 1]
	// }

	// return append(aryA[:idxA], aryA[idxA+1:]...)

}

func BitXor(p interface{}, v interface{}) interface{} {
	switch p.(type) {
	case int:
		return p.(int) ^ v.(int)
	case int64:
		return p.(int64) ^ v.(int64)
	case int32:
		return p.(int32) ^ v.(int32)
	case int16:
		return p.(int16) ^ v.(int16)
	case int8:
		return p.(int8) ^ v.(int8)
	case uint64:
		return p.(uint64) ^ v.(uint64)
	case uint32:
		return p.(uint32) ^ v.(uint32)
	case uint16:
		return p.(uint16) ^ v.(uint16)
	case uint8:
		return p.(uint8) ^ v.(uint8)
	case uint:
		return p.(uint) ^ v.(uint)
	}

	return 0
}

func ToPointerStringArray(aryA []string) *[]string {
	return &aryA
}

func ToPointerFloat64Array(aryA []float64) *[]float64 {
	return &aryA
}

// ParseHexColor inspired by gg
func ParseHexColor(x string) (r, g, b, a int) {
	x = strings.TrimPrefix(x, "#")
	a = 255
	if len(x) == 3 {
		format := "%1x%1x%1x"
		fmt.Sscanf(x, format, &r, &g, &b)
		r |= r << 4
		g |= g << 4
		b |= b << 4
	}
	if len(x) == 6 {
		format := "%02x%02x%02x"
		fmt.Sscanf(x, format, &r, &g, &b)
	}
	if len(x) == 8 {
		format := "%02x%02x%02x%02x"
		fmt.Sscanf(x, format, &r, &g, &b, &a)
	}
	return
}

// DeepClone deep copies original and returns the copy as an interface.
func DeepClone(original interface{}) (copy interface{}) {
	if original == nil {
		return nil
	}
	value := reflect.ValueOf(original)
	return deepCopy(value).Interface()
}

// DeepCopyFromTo deep copies original and assigns the copy to the copy argument (pointer).
func DeepCopyFromTo(original, copy interface{}) error {
	if original == nil {
		copy = nil
		return nil
	} else if copy == nil { // TODO try to initialize it here
		return fmt.Errorf("FromTo: copy target is nil, it should be a valid pointer")
		// copyValue := reflect.New(value.Type().Elem()).Elem()
		// copy = copyValue.Interface()
	}
	copyValue := reflect.ValueOf(copy)
	if copyValue.Kind() != reflect.Ptr {
		return fmt.Errorf("FromTo: copy target type %T and not a pointer", copy)
	}
	value := reflect.ValueOf(original)
	if value.Kind() == reflect.Ptr {
		if value.IsNil() {
			copy = nil // TODO return typed nil
			return nil
		}
		value = value.Elem()
	}
	copyValue.Elem().Set(deepCopy(value))
	return nil
}

func deepCopy(original reflect.Value) reflect.Value {
	switch original.Kind() {
	case reflect.Slice:
		return deepCopySlice(original)
	case reflect.Map:
		return deepCopyMap(original)
	case reflect.Ptr:
		return deepCopyPointer(original)
	case reflect.Struct:
		return deepCopyStruct(original)
	case reflect.Chan:
		return deepCopyChan(original)
	case reflect.Array:
		return deepCopyArray(original)
	default:
		return forceCopyValue(original)
	}
}

// forceCopyValue simply creates a new pointer and sets its value to the original.
func forceCopyValue(original reflect.Value) reflect.Value {
	originalType := original.Type()
	newPointer := reflect.New(originalType)
	newPointer.Elem().Set(original)
	return newPointer.Elem()
}

func deepCopySlice(original reflect.Value) reflect.Value {
	if original.IsNil() {
		return original
	}
	copy := reflect.MakeSlice(original.Type(), 0, 0)
	for i := 0; i < original.Len(); i++ {
		elementCopy := deepCopy(original.Index(i))
		copy = reflect.Append(copy, elementCopy)
	}
	return copy
}

func deepCopyArray(original reflect.Value) reflect.Value {
	if original.Len() == 0 {
		// it cannot be changed anyway, so we can return the original
		return original
	}
	elementType := original.Index(0).Type()
	arrayType := reflect.ArrayOf(original.Len(), elementType)
	newPointer := reflect.New(arrayType)
	copy := newPointer.Elem()
	for i := 0; i < original.Len(); i++ {
		subCopy := deepCopy(original.Index(i))
		copy.Index(i).Set(subCopy)
	}
	return copy
}

func deepCopyMap(original reflect.Value) reflect.Value {
	if original.IsNil() {
		return original
	}
	keyType := original.Type().Key()
	valueType := original.Type().Elem()
	mapType := reflect.MapOf(keyType, valueType)
	copy := reflect.MakeMap(mapType)
	for _, key := range original.MapKeys() {
		value := deepCopy(original.MapIndex(key))
		copy.SetMapIndex(key, value)
	}
	return copy
}

func deepCopyPointer(original reflect.Value) reflect.Value {
	if original.IsNil() {
		return original
	}
	element := original.Elem()
	copy := reflect.New(element.Type())
	copyElement := deepCopy(element)
	copy.Elem().Set(copyElement)
	return copy
}

func deepCopyStruct(original reflect.Value) reflect.Value {
	copy := reflect.New(original.Type()).Elem()
	copy.Set(original)
	for i := 0; i < original.NumField(); i++ {
		fieldValue := copy.Field(i)
		fieldValue = reflect.NewAt(fieldValue.Type(), unsafe.Pointer(fieldValue.UnsafeAddr())).Elem()
		fieldValue.Set(deepCopy(fieldValue))
	}
	return copy
}

func deepCopyChan(original reflect.Value) reflect.Value {
	return reflect.MakeChan(original.Type(), original.Cap())
}

type PlainAuth struct {
	identity, username, password string
	host                         string
}

type ServerInfo struct {
	Name string   // SMTP server name
	TLS  bool     // using TLS, with valid certificate for Name
	Auth []string // advertised authentication mechanisms
}

// PlainAuth get plain auth
func GetPlainAuth(identity, username, password, host string) smtp.Auth {
	return &PlainAuth{identity, username, password, host}
}

func isLocalhost(name string) bool {
	return name == "localhost" || name == "127.0.0.1" || name == "::1"
}

func (a *PlainAuth) Start(server *smtp.ServerInfo) (string, []byte, error) {
	// Must have TLS, or else localhost server.
	// Note: If TLS is not true, then we can't trust ANYTHING in ServerInfo.
	// In particular, it doesn't matter if the server advertises PLAIN auth.
	// That might just be the attacker saying
	// "it's ok, you can trust me with your password."
	// if !server.TLS && !isLocalhost(server.Name) {
	// 	return "", nil, errors.New("unencrypted connection")
	// }
	if server.Name != a.host {
		return "", nil, errors.New("wrong host name")
	}
	resp := []byte(a.identity + "\x00" + a.username + "\x00" + a.password)
	return "PLAIN", resp, nil
}

func (a *PlainAuth) Next(fromServer []byte, more bool) ([]byte, error) {
	command := string(fromServer)
	command = strings.TrimSpace(command)
	command = strings.TrimSuffix(command, ":")
	command = strings.ToLower(command)

	if more {
		if command == "username" {
			return []byte(fmt.Sprintf("%s", a.username)), nil
		} else if command == "password" {
			return []byte(fmt.Sprintf("%s", a.password)), nil
		} else {
			// We've already sent everything.
			return nil, fmt.Errorf("unexpected server challenge: %s", command)
		}
	}
	return nil, nil
}

type LoginAuth struct {
	username, password string
}

func GetLoginAuth(username, password string) smtp.Auth {
	return &LoginAuth{username, password}
}

func (a *LoginAuth) Start(server *smtp.ServerInfo) (string, []byte, error) {
	return "LOGIN", nil, nil
}

func (a *LoginAuth) Next(fromServer []byte, more bool) ([]byte, error) {
	command := string(fromServer)
	command = strings.TrimSpace(command)
	command = strings.TrimSuffix(command, ":")
	command = strings.ToLower(command)

	if more {
		if command == "username" {
			return []byte(fmt.Sprintf("%s", a.username)), nil
		} else if command == "password" {
			return []byte(fmt.Sprintf("%s", a.password)), nil
		} else {
			// We've already sent everything.
			return nil, fmt.Errorf("unexpected server challenge: %s", command)
		}
	}
	return nil, nil
}

// sock5 related

func StartSocksServer(optionsA ...string) error {
	ipT := GetSwitchWithDefaultValue(optionsA, "-ip=", "0.0.0.0")
	portT := GetSwitchWithDefaultValue(optionsA, "-port=", "7480")
	passwordT := GetSwitchWithDefaultValue(optionsA, "-password=", "acb123!@#")
	verboseT := IfSwitchExistsWhole(optionsA, "-verbose")

	lenT := len(passwordT)

	if lenT < 16 {
		passwordT = passwordT + strings.Repeat("z", 16-lenT)
	} else if lenT > 16 {
		passwordT = passwordT[0:16]
	}

	remote, err := net.Listen("tcp", fmt.Sprintf("%s:%s", ipT, portT))

	if err != nil {
		return err
	}

	if verboseT {
		Pl("Start server on %v:%v", ipT, portT)
	}

	for {
		conn, err := remote.Accept()
		if err != nil {
			return Errf("accept err: %v", err)
		} else {
			if verboseT {
				Pl("Client connected: %v", conn.RemoteAddr())
			}
			socks.OpenRemoteTunnel(conn, passwordT)
		}
	}

}

func StartSocksClient(optionsA ...string) error {
	remoteIpT := GetSwitchWithDefaultValue(optionsA, "-remoteIp=", "0.0.0.0")
	remotePortT := GetSwitchWithDefaultValue(optionsA, "-remotePort=", "7480")
	localIpT := GetSwitchWithDefaultValue(optionsA, "-localIp=", "0.0.0.0")
	localPortT := GetSwitchWithDefaultValue(optionsA, "-localPort=", "7481")
	passwordT := GetSwitchWithDefaultValue(optionsA, "-password=", "acb123!@#")
	verboseT := IfSwitchExistsWhole(optionsA, "-verbose")

	lenT := len(passwordT)

	if lenT < 16 {
		passwordT = passwordT + strings.Repeat("z", 16-lenT)
	} else if lenT > 16 {
		passwordT = passwordT[0:16]
	}

	local, err := net.Listen("tcp", fmt.Sprintf("%s:%s", localIpT, localPortT))
	if err != nil {
		return err
	}

	if verboseT {
		Pl("Start socks proxy on %v:%v, remote server: %v: %v", localIpT, localPortT, remoteIpT, remotePortT)
	}

	for {
		conn, err := local.Accept()
		if err != nil {
			return Errf("accept err: %v", err)
		} else {
			if verboseT {
				Pl("Client connected: %v", conn.RemoteAddr())
			}
			socks.OpenLocalTunnel(conn, fmt.Sprintf("%s:%s", remoteIpT, remotePortT), passwordT)
		}
	}

}

// Transparent proxy related

func copyWR(w io.WriteCloser, r io.Reader) {
	_, err := io.Copy(w, r)
	if err != nil {
		Pl("failed to copy: %v", err)
	}
	w.Close()
}

func forwardConn(lc net.Conn, server string, verboseA bool) {
	defer lc.Close()

	rc, err := net.Dial("tcp", server)
	if err != nil {
		if verboseA {
			Pl("failed to dial: %v", err)
		}
		return
	}

	if verboseA {
		Pl("Forwarding connection to %v", server)
	}
	go copyWR(rc, lc)

	copyWR(lc, rc)

	if verboseA {
		Pl("Terminated:  %s -> %s ", lc.RemoteAddr(), server)
	}
}

func StartTransparentProxy(local, server string, optionsA ...string) error {
	verboseT := IfSwitchExistsWhole(optionsA, "-verbose")

	l, err := net.Listen("tcp", local)
	if err != nil {
		if verboseT {
			Pl("failed to listen: %v", err)
		}

		return Errf("failed to listen: %v", err)
	}

	defer l.Close()

	if verboseT {
		Pl("Listening on %v", l.Addr())
	}

	for {
		conn, err := l.Accept()
		if err != nil {
			if verboseT {
				Pl("failed to accept: %v", err)
			}
		}

		if verboseT {
			Pl("New connection from %v", conn.RemoteAddr())
		}

		go forwardConn(conn, server, verboseT)
	}
}

func StartTransparentProxy2(localA, remoteA string, optionsA ...string) error {
	verboseT := IfSwitchExistsWhole(optionsA, "-verbose")

	listener, err := net.Listen("tcp", localA)
	if err != nil {
		if verboseT {
			Pl("Failed to setup listener: %v", err)
		}
		return Errf("Failed to setup listener: %v", err)
	}

	defer listener.Close()

	if verboseT {
		Pl("Listen on: %v:%v", listener.Addr(), "")
	}

	for {
		conn, err := listener.Accept()
		if err != nil {
			if verboseT {
				Pl("Failed to accept connection: %v", err)
			}
			return Errf("ERROR: failed to accept listener: %v", err)
		}

		// if verboseT {
		// 	Pl("Accepted connection on %v from %v", conn.LocalAddr(), conn.RemoteAddr())
		// }

		go func(connA net.Conn, remote1A string) {
			client, err := net.Dial("tcp", remote1A)
			if err != nil {
				if verboseT {
					Pl("Dial failed: %v", err)
				}
				return
			}

			if verboseT {
				Pl("Connected on %v from %v", connA.LocalAddr(), conn.RemoteAddr())
			}

			go func() {
				defer client.Close()
				defer conn.Close()
				io.Copy(client, conn)
			}()
			go func() {
				defer client.Close()
				defer conn.Close()
				io.Copy(conn, client)
			}()

		}(conn, remoteA)
	}
}
