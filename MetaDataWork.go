// #=====
package MetaDataWork

import (
	//	"encoding"
	"bytes"
	"encoding"
	"encoding/binary"
	"fmt"
	"io/ioutil"
	"log"
	"math"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf16"
	"unicode/utf8"

	//	"time"
	"encoding/json"
	//"projects/ParseDBA"
	"context"
	"database/sql"

	"github.com/softlandia/cpd"
	"golang.org/x/text/encoding/charmap"

	//	"golang.org/x/tools/go/analysis/passes/nilness"
	//"honnef.co/go/tools/analysis/facts/nilness"
	//mssql "github.com/denisenkom/go-mssqldb"
	mssql "github.com/microsoft/go-mssqldb"
	"github.com/oartemyev/ParseDBA"
	"github.com/richardlehane/mscfb"
)

// =======================  НАЧАЛО КЛАССА Storage ===========================================
//
// DirectoryEntryTypes
const (
	UNKNOWN      = 0
	STORAGE      = 1
	STREAM       = 2
	ROOT_STORAGE = 5
)

// SectorNumbers
// const uint32 (
//
//	FREESECT     = -1
//	END_OF_CHAIN = -2
//	FATSECT      = -3
//	DIFSECT      = -2
//	MAX_SEC_NUM  = -6
//
// )
var FREESECT uint32 = 4294967295     // 0xFFFFFFFF
var END_OF_CHAIN uint32 = 4294967294 // 0xFFFFFFFE
var FATSECT uint32 = 4294967293      // 0xFFFFFFFD
var DIFSECT uint32 = 4294967292      // 0xFFFFFFFC
var MAX_SEC_NUM uint32 = 4294967290  // 0xFFFFFFFA

type DirectoryEntry struct {
	cfb                                         *Storage
	name                                        []byte
	name_text                                   string
	name_len                                    int
	object_type                                 int
	color_flag                                  int
	sibling_left_id, sibling_right_id, child_id int32
	clsid_id                                    []byte
	state_bits                                  int32
	creation_time                               int64
	modified_time                               int64
	starting_sector_location                    int32
	stream_size                                 int64
}

type ShortDate struct {
	time.Time
}

const layout = "2006-01-02 15:04:05"
const layoutShortDate = "2006-01-02"

func (c *ShortDate) UnmarshalJSON(b []byte) (err error) {
	s := strings.Trim(string(b), `"`) // remove quotes
	if s == "null" {
		return
	}
	arr := strings.Split(s, " ")
	c.Time, err = time.Parse(layoutShortDate, arr[0])
	return
}

func (c ShortDate) MarshalJSON() ([]byte, error) {
	//if c.Time.IsZero() || (c.Time.Year() == 2000 && c.Time.Day() == 1 && c.Time.Month() == 0 && c.Time.Hour() == 0) {
	// if c.Time.IsZero() || (c.Time.Year() == 1 && c.Time.Day() == 1) {
	// 	fmt.Println(c.Time.Year(), c.Time.Month(), c.Time.Day(), c.Time.Hour(), c.Time.Minute(), c.Time.Second())
	// 	//var t time.Time `json:"t,omitempty"`
	// 	//return json.Marshal(t)
	// 	return []byte{}, nil
	// }
	if c.Time.IsZero() {
		return []byte("null"), nil
	}
	return []byte(fmt.Sprintf(`"%s"`, c.Time.Format(layoutShortDate))), nil
}

func (c ShortDate) GetTime() time.Time {
	return c.Time
}

// var minor_version, major_version int16
// var bom, sector_shift_exp, mini_sector_shift_exp int16
var sector_size, mini_sector_size int16
var binary_data []byte

// var number_of_directory_sectors, number_of_FAT_sectors, first_directory_sector_location,
// 	transaction_signature_number, mini_stream_cutoff_size, first_Mini_FAT_sector_location,
// 	number_of_Mini_FAT_sectors, first_DIFAT_sector_location, number_of_DIFAT_sectors

var DIFAT_sectors []int32
var DIFAT []int32
var FAT []int32
var FAT_sectors []int32

// var miniFAT []int32
var max_sector_index uint32

//var directory_entries []DirectoryEntry
//var directory_entries_id_by_name map[string]int

var ObjectsByDescr map[string]interface{}
var ObjectsByID map[string]interface{}

type Storage struct {
	binary_data []byte

	minor_version, major_version                 uint16
	bom, sector_shift_exp, mini_sector_shift_exp uint16
	sector_size, mini_sector_size                uint16

	number_of_directory_sectors, number_of_FAT_sectors, first_directory_sector_location,
	transaction_signature_number, mini_stream_cutoff_size, first_Mini_FAT_sector_location,
	first_DIFAT_sector_location,
	max_sector_index int32

	number_of_DIFAT_sectors    uint32
	number_of_Mini_FAT_sectors uint32

	DIFAT_sectors []int32
	DIFAT         []int32
	FAT           []int32
	FAT_sectors   []int32
	miniFAT       []int32

	directory_entries            []DirectoryEntry
	directory_entries_id_by_name map[string]int

	root   *Storage
	curDir int
}

type Stream struct {
	root   *Storage
	curDir int
}

func DirectoryEntryTypes(i int) string {
	if i == int(ROOT_STORAGE) {
		return "ROOT_STORAGE"
	}
	if i == int(STORAGE) {
		return "STORAGE"
	}
	if i == int(STREAM) {
		return "STREAM"
	}
	if i == int(UNKNOWN) {
		return "UNKNOWN"
	}

	return "ERROR ENTRY TYPE " + IntToString(i)
}

//	func is_valid(sec_num int32) bool {
//		return uint32(sec_num) < MAX_SEC_NUM
//	}
func DecodeUTF16(b []byte) string {
	utf := make([]uint16, (len(b)+(2-1))/2)
	o := binary.BigEndian //binary.LittleEndian
	for i := 0; i+(2-1) < len(b); i += 2 {
		utf[i/2] = o.Uint16(b[i:])
	}
	if len(b)/2 < len(utf) {
		utf[len(utf)-1] = utf8.RuneError
	}
	return string(utf16.Decode(utf))
}
func UTF16ToString(b []byte) (string, error) {

	content := string(b)
	// Декодировать в unicode
	decoder := charmap.Windows1250.NewDecoder()
	reader := decoder.Reader(strings.NewReader(content))
	b1, err := ioutil.ReadAll(reader)

	return string(b1), err
}

func ConvertUtf16ToUtf8(b []byte) string {
	s := string(b)
	s = cpd.DecodeUTF16le(s)

	return s
}

// Contains указывает, содержится ли x в a.
func ContainsInt32(a []int32, x int32) bool {
	for _, n := range a {
		if x == n {
			return true
		}
	}
	return false
}

func sec_num_to_offset(sector_number int32) int32 {
	return (sector_number + 1) * int32(sector_size)
}

func Sec_num_to_offset(sector_number int32, sector_size int32) int32 {
	return (sector_number + 1) * int32(sector_size)
}

func sector(sector_number int32) []byte {
	if (0 <= sector_number) && (uint32(sector_number) <= max_sector_index) {
		return binary_data[sec_num_to_offset(sector_number):sec_num_to_offset(sector_number+1)]
	}

	panic(fmt.Sprintf("Sector %d out of file", sector_number))
}

func read_sector_chain(start_sector_index int32) []byte {
	chain := []byte{}
	read_sectors_indexes := make(map[int32]bool)
	cur_sector := start_sector_index
	for uint32(cur_sector) != END_OF_CHAIN {
		chain = append(chain, sector(cur_sector)...)
		read_sectors_indexes[cur_sector] = true
		next_sector := FAT[cur_sector]
		if read_sectors_indexes[next_sector] {
			panic(fmt.Sprintf("Detected loop in sector chain, starting from sector %d", next_sector))
		}
		cur_sector = next_sector
	}

	return chain
}

func (t *Storage) Sector(sector_number int32) []byte {
	if (0 <= sector_number) && (sector_number <= t.max_sector_index) {

		// var ddd = t.binary_data[Sec_num_to_offset(sector_number, int32(t.sector_size)):Sec_num_to_offset(sector_number+1, int32(t.sector_size))]
		// fmt.Printf("len(ddd)=%d", len(ddd))
		//fmt.Printf("sector_number=%d sec_num_to_offset(sector_number)=%d sec_num_to_offset(sector_number+1)=%d\n", sector_number, Sec_num_to_offset(sector_number, int32(t.sector_size)), Sec_num_to_offset(sector_number+1, int32(t.sector_size)))

		return t.binary_data[Sec_num_to_offset(sector_number, int32(t.sector_size)):Sec_num_to_offset(sector_number+1, int32(t.sector_size))]
	}

	panic(fmt.Sprintf("Sector %d out of file max_sector_index=%d", sector_number, t.max_sector_index))
}

func (t *Storage) Read_sector_chain(start_sector_index int32) []byte {
	chain := []byte{}
	read_sectors_indexes := make(map[int32]bool)
	cur_sector := start_sector_index
	for uint32(cur_sector) != END_OF_CHAIN {
		chain = append(chain, t.Sector(cur_sector)...)
		read_sectors_indexes[cur_sector] = true
		next_sector := t.FAT[cur_sector]
		if read_sectors_indexes[next_sector] {
			panic(fmt.Sprintf("Detected loop in sector chain, starting from sector %d", next_sector))
		}
		cur_sector = next_sector
	}

	return chain
}

// Equal проверяет, что a и b содержат одинаковые элементы.
// nil аргумент эквивалентен пустому срезу.
func EqualByte(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i, v := range a {
		if v != b[i] {
			return false
		}
	}
	return true
}

func ReadInt16(b []byte) int16 {
	var i int16
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadInt32(b []byte) int32 {
	var i int32
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadInt64(b []byte) int64 {
	var i int64
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadInt32Array(b []byte, len int) []int32 {
	var i int32
	var k int
	bb := []int32{}
	var err error
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	for k = 0; k < len; k++ {
		err = binary.Read(buf, binary.LittleEndian, &i)
		if err != nil {
			panic(err)
		}
		bb = append(bb, i)
	}

	return bb

}

func ReadUInt16(b []byte) uint16 {
	var i uint16
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadUInt32(b []byte) uint32 {
	var i uint32
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadUInt64(b []byte) uint64 {
	var i uint64
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	err := binary.Read(buf, binary.LittleEndian, &i)
	if err != nil {
		panic(err)
	}

	return i

}

func ReadUInt32Array(b []byte, len int) []uint32 {
	var i uint32
	var k int
	bb := []uint32{}
	var err error
	buf := bytes.NewBuffer([]byte{})
	buf.Write(b)
	//	err = binary.Read(buf, binary.BigEndian, &minor_version)
	for k = 0; k < len; k++ {
		err = binary.Read(buf, binary.LittleEndian, &i)
		if err != nil {
			panic(err)
		}
		bb = append(bb, i)
	}

	return bb

}

func StgOpenStorage(fileName string) *Storage {

	data, err := ioutil.ReadFile(fileName)
	if err != nil {
		return nil
	}
	if len(data) < 512 {
		return nil
	}

	stg := new(Storage)
	stg.root = nil
	stg.curDir = 0
	stg.binary_data = data

	stg.minor_version = ReadUInt16(data[24:26])
	stg.major_version = ReadUInt16(data[26:28])

	stg.bom = ReadUInt16(data[28:30])
	stg.sector_shift_exp = ReadUInt16(data[30:32])
	stg.mini_sector_shift_exp = ReadUInt16(data[32:34])

	if !((stg.sector_shift_exp == 9 && stg.major_version == 3) || (stg.sector_shift_exp == 12 && stg.major_version == 4)) {
		//panic("Sector shift must be 2^9=512 for v3 and 2^12=4096 for v4")
		return nil
	}

	//	stg.sector_size = int16(math.Pow(2, float64(stg.sector_shift_exp)))
	stg.sector_size = uint16(math.Pow(2, float64(stg.sector_shift_exp-1)))
	stg.mini_sector_size = uint16(math.Pow(2, float64(stg.mini_sector_shift_exp)))

	stg.number_of_directory_sectors = ReadInt32(data[40:44])
	stg.number_of_FAT_sectors = ReadInt32(data[44:48])
	stg.first_directory_sector_location = ReadInt32(data[48:52])
	stg.transaction_signature_number = ReadInt32(data[52:56])
	stg.mini_stream_cutoff_size = int32(ReadUInt32(data[56:60]))
	stg.first_Mini_FAT_sector_location = ReadInt32(data[60:64])
	stg.number_of_Mini_FAT_sectors = ReadUInt32(data[64:68])
	stg.first_DIFAT_sector_location = ReadInt32(data[68:72])
	stg.number_of_DIFAT_sectors = ReadUInt32(data[72:76])

	stg.DIFAT = ReadInt32Array(data[76:512], 109)

	stg.max_sector_index = int32(len(data))/int32(stg.sector_size) - 2
	stg.DIFAT_sectors = []int32{}

	//fmt.Printf("stg.first_DIFAT_sector_location=%d int32(math.Abs(MAX_SEC_NUM))=%d %d", stg.first_DIFAT_sector_location, int32(math.Abs(MAX_SEC_NUM)), stg.max_sector_index)

	//	if stg.first_DIFAT_sector_location <= int32(math.Abs(MAX_SEC_NUM)) {
	if stg.first_DIFAT_sector_location <= stg.max_sector_index {
		n_sec := 0
		cur_difat_sec := stg.first_DIFAT_sector_location
		for (int32(math.Abs(float64(cur_difat_sec))) <= stg.max_sector_index) && (cur_difat_sec != int32(END_OF_CHAIN)) {
			if ContainsInt32(stg.DIFAT_sectors, cur_difat_sec) {
				panic(fmt.Sprintf("There's a loop in DIFAT chain on %d step. Next sector: %d", n_sec, cur_difat_sec))
			}
			stg.DIFAT_sectors = append(stg.DIFAT_sectors, cur_difat_sec)
			n_sec += 1
			entries := ReadInt32Array(stg.Sector(cur_difat_sec), int(stg.sector_size/4))

			//fmt.Printf("\n")
			//fmt.Print(entries)
			//fmt.Printf("\n")

			stg.DIFAT = append(stg.DIFAT, entries...)
			cur_difat_sec = entries[len(entries)-1]
		}
	}
	//fmt.Print(stg.DIFAT)

	//fmt.Printf("\n2) Размер DIFAT %d\n", len(stg.DIFAT))

	//fmt.Print("Reading FAT...\n")
	for i := 0; i < int(stg.number_of_FAT_sectors); i++ {
		//fmt.Printf("i=%d\n", i)
		stg.FAT_sectors = append(stg.FAT_sectors, stg.DIFAT[i])
		stg.FAT = append(stg.FAT, ReadInt32Array(stg.Sector(stg.DIFAT[i]), int(stg.sector_size/4))...)
	}
	//fmt.Printf("3) Размер FAT %d\n", len(stg.FAT))

	//fmt.Print("Reading miniFAT...\n")
	cur_sec := stg.first_Mini_FAT_sector_location
	for cur_sec != int32(END_OF_CHAIN) {
		stg.miniFAT = append(stg.miniFAT, ReadInt32Array(stg.Sector(cur_sec), int(stg.sector_size/4))...)
		cur_sec = stg.FAT[cur_sec]
	}
	//fmt.Printf("4) Размер miniFAT %d\n", len(stg.miniFAT))

	// read directory
	directory_binary := stg.Read_sector_chain(stg.first_directory_sector_location)

	stg.directory_entries_id_by_name = make(map[string]int)
	for i := 0; i < len(directory_binary); {
		de := new(DirectoryEntry)

		//fmt.Printf("i=%d ", i)

		de.InitDirectoryEntry(stg, directory_binary[i:i+128])
		if de.name_len != 0 {
			stg.directory_entries = append(stg.directory_entries, *de)
			stg.directory_entries_id_by_name[de.name_text] = i / 128
			//break
			//continue
		}

		i += 128
	}

	return stg
}

func FindStorage(st *Storage, direcoryID int, nameDir string) int32 {
	var de, deDef DirectoryEntry

	de = st.directory_entries[direcoryID]
	if de.child_id == -1 {
		return -1
	}
	if de.object_type == int(STREAM) {
		return -1
	}

	curDir := de.child_id
	de = st.directory_entries[de.child_id]
	deDef = de

	for de.sibling_left_id != -1 {
		//print_dirEntry(&de, " ", 0)
		if de.name_text == nameDir {
			return curDir
		}
		curDir = de.sibling_left_id
		de = st.directory_entries[de.sibling_left_id]
	}
	if deDef.sibling_right_id == -1 {
		return -1
	}

	de = deDef
	curDir = de.child_id
	de = st.directory_entries[deDef.sibling_right_id]
	for de.sibling_right_id != -1 {
		//print_dirEntry(&de, " ", 0)
		if de.name_text == nameDir {
			return curDir
		}
		curDir = de.sibling_right_id
		de = st.directory_entries[de.sibling_right_id]
	}
	if de.name_text == nameDir {
		return curDir
	}

	return -1
}

func (t *Storage) OpenStorage(nameStorage string) *Storage {

	var root *Storage
	if t.root == nil {
		root = t
	} else {
		root = t.root
	}

	st := t
	nameDirs := strings.Split(nameStorage, "\\")
	if len(nameDirs) > 1 {
		for i := 0; i < len(nameDirs)-1; i++ {
			st = st.OpenStorage(nameDirs[i])
			if st == nil {
				return nil
			}
		}
		nameStorage = nameDirs[len(nameDirs)-1]
	}

	var ndxDir = FindStorage(root, t.curDir, nameStorage)
	if ndxDir == -1 {
		return nil
	}

	var de = root.directory_entries[ndxDir]
	if de.object_type == int(STREAM) {
		return nil
	}

	stRet := new(Storage)
	stRet.root = root
	stRet.curDir = int(ndxDir)

	return stRet
}

func (t *DirectoryEntry) InitDirectoryEntry(_cfb *Storage, binary_data []byte) {
	if len(binary_data) != 128 {
		panic(fmt.Sprintf("Directory entry len is %d, not equal 128", len(binary_data)))
	}
	t.cfb = _cfb
	t.name = binary_data[:64]
	//	t.name_text = DecodeUTF16(binary_data[:64])
	//	t.name_text, _ = UTF16ToString(binary_data[:64])
	t.name_len = int(ReadInt16(binary_data[64:66]))
	if t.name_len == 0 {
		return
	}
	t.name_text = ConvertUtf16ToUtf8(binary_data[:t.name_len-2])
	t.object_type = int(binary_data[66])
	t.color_flag = int(binary_data[67])
	t.sibling_left_id = ReadInt32(binary_data[68:72])
	t.sibling_right_id = ReadInt32(binary_data[72:76])
	t.child_id = ReadInt32(binary_data[76:80])
	t.clsid_id = binary_data[80:96]
	t.state_bits = ReadInt32(binary_data[96:100])
	t.creation_time = ReadInt64(binary_data[100:108])
	t.modified_time = ReadInt64(binary_data[108:116])
	t.starting_sector_location = ReadInt32(binary_data[116:120])
	t.stream_size = ReadInt64(binary_data[120:128])
}

func (t *Storage) OpenStream(nameStream string) *Stream {

	var root *Storage
	if t.root == nil {
		root = t
	} else {
		root = t.root
	}

	st := t
	nameDirs := strings.Split(nameStream, "\\")
	if len(nameDirs) > 1 {
		for i := 0; i < len(nameDirs)-1; i++ {
			st = st.OpenStorage(nameDirs[i])
			if st == nil {
				return nil
			}
		}
		nameStream = nameDirs[len(nameDirs)-1]
	}

	var ndxDir = FindStorage(root, t.curDir, nameStream)
	if ndxDir == -1 {
		return nil
	}

	var de = root.directory_entries[ndxDir]
	if de.object_type != int(STREAM) {
		return nil
	}

	stRet := new(Stream)
	stRet.root = root
	stRet.curDir = int(ndxDir)

	return stRet

}

func (t *Stream) GetSize() int32 {
	var de = t.root.directory_entries[t.curDir]

	return int32(de.stream_size)
}

func (t *Stream) Read(c []byte, lSize int32) []byte {
	i := t.GetSize()
	if i < lSize {
		lSize = i
	}
	var de = t.root.directory_entries[t.curDir]
	bt := t.root.Read_sector_chain(de.starting_sector_location)
	//c = bt[:lSize]

	return bt[:lSize]
}

//=======================  КОНЕЦ КЛАССА Storage ===========================================

// =======================  НАЧАЛО MetaDataWork ===========================================
type TTokenType int

const (
	TOK_None         TTokenType = iota
	TOK_OpenBrace    TTokenType = iota
	TOK_CloseBrace   TTokenType = iota
	TOK_QuotedString TTokenType = iota
)

type StateCMMS int

const (
	start         StateCMMS = iota
	objects       StateCMMS = iota
	wait_obj_type StateCMMS = iota
	end           StateCMMS = iota
)

type TypeMD int

const (
	md_None       TypeMD = iota
	md_Const      TypeMD = iota
	md_Sprav      TypeMD = iota
	md_Doc        TypeMD = iota
	md_Enum       TypeMD = iota
	md_EnumVal    TypeMD = iota
	md_Register   TypeMD = iota
	md_RegIzm     TypeMD = iota
	md_RegResurs  TypeMD = iota
	md_RegRekv    TypeMD = iota
	md_FldDef     TypeMD = iota
	md_SpravParam TypeMD = iota
	md_DocHead    TypeMD = iota
	md_DocTable   TypeMD = iota
)

type LexerState int

const (
	in_string        LexerState = 1
	end_string_check LexerState = 2
)

type PeriodType int

const ( //PeriodType
	eDay         PeriodType = iota
	eWeek        PeriodType = iota
	eMonth       PeriodType = iota
	eQuart       PeriodType = iota
	eYear        PeriodType = iota
	e_NotUsed    PeriodType = iota
	eTenDays     PeriodType = iota
	eFiveDays    PeriodType = iota
	eFifteenDays PeriodType = iota
	e_Document   PeriodType = iota
)

type TTokenStack struct {
	Token string
	Type  TTokenType
}

type Lexer struct {
	fStream  string
	Stack    []TTokenStack
	Position int
}

func NewLexer(st string) *Lexer {
	l := new(Lexer)
	l.fStream = st
	l.Position = 0

	return l
}

func (t *Lexer) Init(st string) {
	t.fStream = st
	t.Stack = make([]TTokenStack, 0)
	t.Position = 0
}

func (t *Lexer) AtStart() bool {
	return t.Position == 0
}

func (t *Lexer) SkipMusor() {
	for ; t.Position < len(t.fStream); t.Position++ {
		if t.fStream[t.Position] == '{' {
			break
		}
	}
}

func (t *Lexer) PopMMSToken(Token string, TokenType TTokenType) (string, TTokenType, bool) {
	if len(t.Stack) == 0 {
		return Token, TokenType, false
	}
	n := len(t.Stack) - 1
	entry := t.Stack[n]
	t.Stack = t.Stack[:n]

	return entry.Token, entry.Type, true
}

func (t *Lexer) PushMMSToken(Token string, TokenType TTokenType) {
	entry := new(TTokenStack)
	entry.Token = Token
	entry.Type = TokenType
	t.Stack = append(t.Stack, *entry)
}

func (t *Lexer) FilePosition() int {
	return t.Position
}

func (t *Lexer) GetMMSToken(Token string, TokenType TTokenType) (string, TTokenType, bool) {
	var ret bool
	Token, TokenType, ret = t.PopMMSToken(Token, TokenType)
	if ret {
		return Token, TokenType, ret
	}

	state := LexerState(start)
	Token = ""
	TokenType = TOK_None
	for t.Position < len(t.fStream) {
		//c := t.fStream[t.Position]
		c, width := utf8.DecodeRuneInString(t.fStream[t.Position:])
		t.Position += width

		if c == '\r' {
			continue
		}
		if c == '\n' {
			continue
		}

		if state == LexerState(start) {
			switch c {
			case '"':
				state = in_string
			case '{':
				Token = "{"
				TokenType = TOK_OpenBrace
				return Token, TokenType, true
			case '}':
				Token = "}"
				TokenType = TOK_CloseBrace
				return Token, TokenType, true
			}
		} else if state == LexerState(in_string) {
			if c == '"' {
				state = LexerState(end_string_check)
			} else {
				//Token = Token + Convert.ToChar(c);
				Token = Token + string(c)
			}
		} else if state == LexerState(end_string_check) {
			if c == '"' {
				Token = Token + "\"\""
				state = LexerState(in_string)
			} else {
				t.Position--
				TokenType = TOK_QuotedString
				return Token, TokenType, true
			}
		}
	}

	return Token, TokenType, false
}

type CMMS struct {
	SID      string
	Params   []string
	Children []CMMS
}

func (t *CMMS) _Init() {
	t.SID = ""
}

func NewCMMS(st string) *CMMS {
	c := new(CMMS)
	c.SID = st
	return c
}

func (t *CMMS) CreateChild(s string) *CMMS {
	return NewCMMS(s)
}

func (t *CMMS) SetValue(s string) {
	t.Params = append(t.Params, s)
}

func (t *CMMS) AddChild(s CMMS) {
	t.Children = append(t.Children, s)
}

func (t *CMMS) PrintLog(level int) {
	var i, n int
	str := ""
	nProps := len(t.Children)

	if t.SID == "" {
		str = ""
	} else {
		for i = 0; i < level; i++ {
			str = str + " "
		}
		if len(t.SID) != 0 {
			fmt.Printf("%s%s\n", str, t.SID)
		}
		n = len(t.Params)
		for i = 0; i < n; i++ {
			fmt.Printf("%s%s%s\n", str, str, t.Params[i])
		}
	}

	level++
	for i = 0; i < nProps; i++ {
		t.Children[i].PrintLog(level)
	}
}

func (t *CMMS) ParseMetaData(lex Lexer) Lexer {
	var Child CMMS
	var Token, ObjName string
	var TokType TTokenType
	var state StateCMMS
	var AtSart, ret bool

	AtSart = lex.AtStart()
	if AtSart {
		state = start
		lex.SkipMusor()
	} else {
		state = objects
	}

	Token = ""
	TokType = TOK_None

	for {
		Token, TokType, ret = lex.GetMMSToken(Token, TokType)
		if !ret {
			break
		}
		switch state {
		case start:
			switch TokType {
			case TOK_OpenBrace:
				state = objects
				//default:
			}
		case objects:
			switch TokType {
			case TOK_QuotedString:
				t.SetValue(Token)

			case TOK_OpenBrace:
				state = wait_obj_type

			case TOK_CloseBrace:
				if AtSart {
					state = end
				} else {
					return lex
				}
				//default:
			}

		case wait_obj_type:
			if TokType == TOK_QuotedString {
				ObjName = Token
			} else {
				ObjName = ""
			}

			Child = *t.CreateChild(ObjName)
			lex.PushMMSToken(Token, TokType)
			lex = Child.ParseMetaData(lex)
			t.AddChild(Child)

			state = objects
		}
	}

	return lex
}

type MDRec interface {
	GetType_() string
}

type MetaProps interface { //МетаРеквизит
	GetType() string
	GetLength() int
	GetPeriod() int
	GetVid() int
}

func (t MetaDataWork) PrepareValue(o MetaProps, FirstPart string) string {
	rekv := ""
	if o.GetType() == "N" || o.GetType() == "U" {
		rekv = FirstPart + ".VALUE"
	} else if o.GetType() == "S" {
		rekv = "SUBSTRING(" + FirstPart + ".VALUE,1," + IntToString(o.GetLength()) + ")"
	} else if o.GetType() == "D" {
		rekv = "SUBSTRING(" + FirstPart + ".VALUE,7,4)+SUBSTRING(" + FirstPart + ".VALUE,4,2)+LEFT(" + FirstPart + ".VALUE,2)"
	} else {
		len := 9
		if o.GetVid() == 0 {
			len = len + 4
		}
		rekv = "LEFT(" + FirstPart + ".VALUE," + IntToString(len) + ")"
	}

	return rekv
}

type MDObject struct {
	obj             MDRec
	objDescr, objID string
}

func NewMDObject(_obj MDRec, objDescr string) MDObject {
	var d *MDObject = new(MDObject)

	d.obj = _obj
	d.objDescr = objDescr

	switch obj := _obj.(type) {
	case _MDRec:
		d.objID = obj.SID
	case DocSelRefObj:
		d.objID = obj.SID
	case FormMD:
		d.objID = obj.SID
	case CommonProp:
		d.objID = obj.SID
	case ConstRec:
		d.objID = obj.SID
	case SpravParam:
		d.objID = obj.SID
	case SpravRec:
		d.objID = obj.SID
	}

	//	d.objID = obj.SID

	return *d
}

type _MDRec struct {
	TypeObject                    string
	SID, Desc, Type               string
	ID, Len, Dec, TypeObj, Period int
	ChangeDoc                     int // 1 - ИзменяетсяДокументами
}

func (t _MDRec) GetType() string {

	return t.Type

}

func (t _MDRec) GetType_() string {

	return t.TypeObject

}

func (t _MDRec) GetPeriod() int {

	return t.Period

}

func (t _MDRec) GetLength() int {

	return t.Len

}

func (t _MDRec) GetVid() int {

	return t.ID

}

func NewMDRec() _MDRec {
	t := new(_MDRec)
	t.TypeObject = fmt.Sprintf("%T", t)
	t.SID = ""
	t.Type = ""
	t.Desc = ""
	t.ID = 0
	t.Len = 0
	t.Dec = 0
	t.TypeObj = 0
	t.Period = 0
	t.ChangeDoc = 0

	return *t
}

type DocSelRefObj struct {
	_MDRec
	Comment   string
	OtborNull int // флаг отбора пустых значений
	Param     []string
}

/*
	func (t *DocSelRefObj) GetType() string {
		s := ""
		fmt.Sprintf(s, "%T", t)

		return s
	}
*/
func (t *DocSelRefObj) _Dummy() {}

func NewDocSelRefObj() DocSelRefObj {
	t := new(DocSelRefObj)
	t._MDRec = NewMDRec()
	t.TypeObject = fmt.Sprintf("%T", *t)
	t.Comment = ""
	t.OtborNull = 0

	return *t
}

func NewDocSelRefObj_01(Params []string) DocSelRefObj {
	t := NewDocSelRefObj()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Comment = Params[3]
		t.OtborNull, _ = strconv.Atoi(Params[4])
		t.Type = strings.Trim(Params[5], " ")
		t.TypeObj, _ = strconv.Atoi(Params[6])
	}

	return t
}

func NewDocSelRefObj_02(Params []string, Children []CMMS) DocSelRefObj {
	t := NewDocSelRefObj_01(Params)

	obj := Children[0]
	for j := 0; j < len(obj.Children); j++ {
		tmp := obj.Children[j]
		t.Param = append(t.Param, tmp.SID)
	}

	return t
}

type FormMD struct {
	_MDRec
	Comment string
}

func IntToString(i int) string {
	return fmt.Sprintf("%d", i)
}

/*
	func (t *FormMD) GetType() string {
		s := ""
		fmt.Sprintf(s, "%T", t)

		return s
	}
*/
func (t *FormMD) _Dummy() {}

func NewFormMD() FormMD {
	t := new(FormMD)
	t._MDRec = NewMDRec()
	t.Comment = ""
	t.TypeObject = fmt.Sprintf("%T", *t)

	return *t
}

func NewFormMD_01(Params []string) FormMD {
	t := NewFormMD()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Comment = Params[3]
	}

	return t
}

type CommonProp struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	Otbor   int // Отбор: 1 или 0
}

/*
	func (t *CommonProp) GetType() string {
		s := ""
		fmt.Sprintf(s,"%T", t)

		return s
	}
*/
func (t *CommonProp) _Dummy() {}

func NewCommonProp() CommonProp {
	t := new(CommonProp)
	t._MDRec = NewMDRec()
	t.TypeObject = fmt.Sprintf("%T", *t)
	t.Syn = ""
	t.Comment = ""
	t.Abs = 0
	t.Otbor = 0
	t.Period = 0

	return *t
}

func NewCommonProp_01(Params []string) CommonProp {
	t := NewCommonProp()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Otbor, _ = strconv.Atoi(Params[10])
		t.Period = 0
	}

	return t
}

type ConstRec struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	Dummy   int // Отбор: 1 или 0
}

func (t *ConstRec) _Dummy() {}

func NewConstRec() ConstRec {
	t := new(ConstRec)
	t._MDRec = NewMDRec()
	t.TypeObject = fmt.Sprintf("%T", *t)
	t.Syn = ""
	t.Comment = ""
	t.Abs = 0
	t.Dummy = 0
	t.Period = 0

	return *t
}

func NewConstRec_01(Params []string) ConstRec {
	t := NewConstRec()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Dummy, _ = strconv.Atoi(Params[9])
		t.Period, _ = strconv.Atoi(Params[10])
	}

	return t
}

type MDRecCol struct {
	StrMeta string
	TypeMd  TypeMD

	// NameToID map[string]string
	// IDToName map[string]string
	// RecMD    map[string]interface{}
	NameToID []string
	IDToName []string
	RecMD    []interface{}
}

func NewMDRecCol() MDRecCol {
	m := *new(MDRecCol)

	// //_m := make(map[string]string)
	// m.NameToID = make(map[string]string)
	// //_m = make(map[string]string)
	// m.IDToName = make(map[string]string)
	// //_mm := make(map[string]interface{})
	// m.RecMD = make(map[string]interface{})

	m.StrMeta = ""
	m.TypeMd = md_None

	return m
}

func (t MDRecCol) at(n int) interface{} {
	for _, value := range t.RecMD {
		if n == 0 {
			return value
		}
		if n < 0 {
			break
		}
		n--
	}

	return nil
}

func (t *MDRecCol) Add(sid string, ID string, rc interface{}) MDRecCol {
	// t.RecMD[ID] = rc
	// m := t.NameToID
	// m[strings.ToUpper(sid)] = ID
	// t.NameToID = m
	// m = t.IDToName
	// m[ID] = sid
	// t.IDToName = m
	t.NameToID = append(t.NameToID, strings.ToUpper(sid))
	t.IDToName = append(t.IDToName, ID)
	t.RecMD = append(t.RecMD, rc)

	return *t
}

func (t MDRecCol) GetByName(key string) interface{} {
	//return t.RecMD[t.NameToID[strings.ToUpper(key)]]
	var rr interface{}
	for i := 0; i < len(t.NameToID); i++ {
		if t.NameToID[i] == strings.ToUpper(key) {
			return t.RecMD[i]
		}
	}
	return rr
}

func (t MDRecCol) GetByID(key int) interface{} {
	//return t.RecMD[fmt.Sprintf("%d", key)]
	var rr interface{}
	s := fmt.Sprintf("%d", key)
	for i := 0; i < len(t.NameToID); i++ {
		if t.IDToName[i] == s {
			return t.RecMD[i]
		}
	}
	return rr
}

func (t MDRecCol) Count() int {
	return len(t.RecMD)
}

func (t MDRecCol) NameToId(key string) string {
	//return t.NameToID[strings.ToUpper(key)]
	s := ""
	for i := 0; i < len(t.NameToID); i++ {
		if t.NameToID[i] == strings.ToUpper(key) {
			return t.IDToName[i]
		}
	}
	return s
}

func (t MDRecCol) IdToName(key string) string {
	//return t.IDToName[strings.ToUpper(key)]
	s := ""
	for i := 0; i < len(t.NameToID); i++ {
		if t.IDToName[i] == key {
			return t.NameToID[i]
		}
	}
	return s
}

type SpravParam struct {
	_MDRec
	Syn      string
	Comment  string
	Abs      int // 1 - не отрицательный
	Dummy    int
	ForElem  int // 1 - для элемента
	ForGroup int // 1 - для группы
	Sorted   int // 1 - сортировка
	Otbor    int // 1 - отбор
}

func NewSpravParam() SpravParam {
	s := new(SpravParam)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewSpravParam_01(Params []string) SpravParam {
	t := NewSpravParam()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Dummy, _ = strconv.Atoi(Params[9])
		t.Period, _ = strconv.Atoi(Params[10])
		t.ForGroup, _ = strconv.Atoi(Params[10+2])
		t.ForElem, _ = strconv.Atoi(Params[9+2])
		t.Sorted, _ = strconv.Atoi(Params[10+3])
		t.Otbor, _ = strconv.Atoi(Params[14+2])
		t.ChangeDoc, _ = strconv.Atoi(Params[14+1])
	}

	return t
}

type SpravRec struct {
	_MDRec
	Syn           string
	Comment       string
	ParentID      int //  Числовой идентификатор владельца. Если 0, то справочник не подчинён
	LenCode       int //	Длина кода
	SeriesCode    int //	Серии кодов: 1 - во всём справочнике, 2 - в пределах подчинения
	TypeCode      int //	Тип кода: 1 - текстовый, 2 - числовой
	AutoNum       int //	Атонумерация: 1 - нет; 2 - да
	LenName       int //	Длина наименования
	Levels        int //	Количество уровней
	Uniqal        int //	Уникальность кодов: 1 или 0
	Params, Forms MDRecCol
}

func NewSpravRec() SpravRec {
	t := new(SpravRec)
	t.Params = NewMDRecCol()
	t.Forms = NewMDRecCol()
	t.TypeObject = fmt.Sprintf("%T", *t)

	return *t
}

func NewSpravRec_01(Params []string) SpravRec {
	t := NewSpravRec()

	if len(Params) > 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.ParentID, _ = strconv.Atoi(Params[4])
		t.LenCode, _ = strconv.Atoi(Params[5])
		t.SeriesCode, _ = strconv.Atoi(Params[6])
		t.TypeCode, _ = strconv.Atoi(Params[7])
		t.AutoNum, _ = strconv.Atoi(Params[8])
		t.LenName, _ = strconv.Atoi(Params[9])
		t.Levels, _ = strconv.Atoi(Params[12])
		t.Uniqal, _ = strconv.Atoi(Params[16])
	}

	return t
}

func (t *SpravRec) Add(sID string, ID string, rc interface{}) {
	t.Params.Add(sID, ID, rc)
}

func (t *SpravRec) AddForma(sID string, ID string, rc interface{}) {
	t.Forms.Add(sID, ID, rc)
}

func (t SpravRec) GetRekvCount() int {
	return t.Params.Count()
}

func (t SpravRec) GetRekvByNum(n int) SpravParam {
	if (n < t.Params.Count()) && (n >= 0) {
		i := t.Params.at(n)
		switch tp := i.(type) {
		case SpravParam:
			return tp
		}
	}
	var tp SpravParam
	return tp
}

func (t SpravRec) GetRekvByName(n string) SpravParam {
	nv := strings.ToUpper(strings.Trim(n, " "))
	i := t.Params.GetByName(nv)
	switch tp := i.(type) {
	case SpravParam:
		return tp
	}
	var tp SpravParam
	return tp
}

func (t DocRec) GetDocHeadByName(n string) DocHead {
	nv := strings.ToUpper(n)
	i := t.Heads.GetByName(nv)
	switch tp := i.(type) {
	case DocHead:
		return tp
	}
	var tp DocHead
	return tp
}

func (t DocRec) GetDocTableByName(n string) DocTable {
	nv := strings.ToUpper(n)
	i := t.Table.GetByName(nv)
	switch tp := i.(type) {
	case DocTable:
		return tp
	}
	var tp DocTable
	return tp
}

type EnumVal struct {
	_MDRec
	Descr   string
	Comment string
}

func NewEnumVal() EnumVal {
	s := new(EnumVal)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewEnumVal_01(Params []string) EnumVal {
	t := NewEnumVal()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Comment = Params[3]
		t.Descr = strings.Trim(Params[4], " ")
	}

	return t
}

type EnumRec struct {
	_MDRec
	Syn     string
	Comment string
	Params  MDRecCol
}

func NewEnumRec() EnumRec {
	t := *new(EnumRec)
	t.Params = NewMDRecCol()
	t.TypeObject = fmt.Sprintf("%T", t)

	return t
}

func NewEnumRec_01(Params []string) EnumRec {
	t := NewEnumRec()

	t.Params = NewMDRecCol()
	if len(Params) > 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
	}

	return t
}

func (t EnumRec) Add(sID string, ID string, rc interface{}) EnumRec {
	p := t.Params
	p = p.Add(sID, ID, rc)
	t.Params.IDToName = p.IDToName
	t.Params.NameToID = p.NameToID
	t.Params.RecMD = p.RecMD
	return t
}

type DocHead struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	Itog    int
}

func NewDocHead() DocHead {
	s := new(DocHead)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewDocHead_01(Params []string) DocHead {
	t := NewDocHead()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Itog = 0
		t.Period, _ = strconv.Atoi(Params[9])
	}

	return t
}

type DocTable struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	Itog    int
}

func NewDocTable() DocTable {
	s := new(DocTable)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewDocTable_01(Params []string) DocTable {
	t := NewDocTable()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Itog, _ = strconv.Atoi(Params[9])
		t.Period, _ = strconv.Atoi(Params[10])
	}

	return t
}

type DocRec struct {
	_MDRec
	Syn     string
	Comment string
	LenNum  int //  	Длина номера
	TypeNum int //	Тип номера: 1 - текстовый, 2 - числовой
	//Period		  int //	Периодичность: 0 - по всем данного вида, 1 - в пределах года, 2 - в пределах квартала, 3 - в пределах месяца, 4 - в пределах дня.
	Heads, Table, Forms MDRecCol
}

func NewDocRec() DocRec {
	t := new(DocRec)
	t.Heads = NewMDRecCol()
	t.Table = NewMDRecCol()
	t.Forms = NewMDRecCol()
	t.TypeObject = fmt.Sprintf("%T", *t)

	return *t
}

func NewDocRec_01(Params []string) DocRec {
	t := NewDocRec()

	if len(Params) > 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.LenNum, _ = strconv.Atoi(Params[4])
		t.Period, _ = strconv.Atoi(Params[5])
		t.TypeNum, _ = strconv.Atoi(Params[6])
	}

	return t
}

func (t *DocRec) AddHead(sID string, ID string, rc interface{}) {
	t.Heads = t.Heads.Add(sID, ID, rc)
}

func (t *DocRec) AddTable(sID string, ID string, rc interface{}) {
	t.Table = t.Table.Add(sID, ID, rc)
}
func (t *DocRec) AddForma(sID string, ID string, rc interface{}) {
	t.Forms = t.Forms.Add(sID, ID, rc)
}

type RegIzm struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	OtborDv int // Отбор движений: 1 или 0
	OtborIt int // Отбор итогов: 1 или 0
}

func NewRegIzm() RegIzm {
	s := new(RegIzm)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewRegIzm_01(Params []string) RegIzm {
	t := NewRegIzm()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.OtborDv, _ = strconv.Atoi(Params[10])
		t.OtborIt, _ = strconv.Atoi(Params[11])
	}

	return t
}

type RegRes struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
}

func NewRegRes() RegRes {
	s := new(RegRes)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewRegRes_01(Params []string) RegRes {
	t := NewRegRes()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
	}

	return t
}

type RegReq struct {
	_MDRec
	Syn     string
	Comment string
	Abs     int // 1 - не отрицательный
	Otbor   int // Отбор движений: 1 или 0
}

func NewRegReq() RegReq {
	s := new(RegReq)
	s.TypeObject = fmt.Sprintf("%T", *s)
	return *s
}

func NewRegReq_01(Params []string) RegReq {
	t := NewRegReq()

	if len(Params) != 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Type = strings.Trim(Params[4], " ")
		t.Len, _ = strconv.Atoi(Params[5])
		t.Dec, _ = strconv.Atoi(Params[6])
		t.TypeObj, _ = strconv.Atoi(Params[7])
		t.Abs, _ = strconv.Atoi(Params[8])
		t.Otbor, _ = strconv.Atoi(Params[10])
	}

	return t
}

type RegRec struct {
	_MDRec
	Syn     string
	Comment string
	Oborot  int //  	Оборотный
	Fast    int //	Быстрая обработка движений: 1 или 0
	//Period		  int		//	Периодичность (только для оборотных): Y - год, Q - квартал, M - месяц, C - декада, W - неделя, D - день
	Izm, Resurs, Rekv MDRecCol
}

func NeRegRec() RegRec {
	t := new(RegRec)
	t.Izm = NewMDRecCol()
	t.Resurs = NewMDRecCol()
	t.Rekv = NewMDRecCol()
	t.TypeObject = fmt.Sprintf("%T", *t)

	return *t
}

func NewRegRec_01(Params []string) RegRec {
	t := NeRegRec()

	if len(Params) > 0 {
		t.SID = Params[1]
		t.ID, _ = strconv.Atoi(Params[0])
		t.Syn = Params[2]
		t.Comment = Params[3]
		t.Oborot, _ = strconv.Atoi(Params[4])
		t.Period = int(byte(Params[5][0])) //strconv.Atoi(Params[5])
		t.Fast, _ = strconv.Atoi(Params[6])
	}

	return t
}

func (t *RegRec) AddIzm(sID string, ID string, rc interface{}) {
	t.Izm.Add(sID, ID, rc)
}
func (t *RegRec) AddResurs(sID string, ID string, rc interface{}) {
	t.Resurs.Add(sID, ID, rc)
}
func (t *RegRec) AddRekv(sID string, ID string, rc interface{}) {
	t.Rekv.Add(sID, ID, rc)
}

func GetCMMS_FromString(filename string) CMMS {

	// btStream := []byte(filename)

	// decoder := charmap.Windows1251.NewDecoder()
	// buf := bytes.NewBuffer([]byte{})
	// buf.Write(btStream)

	// reader := decoder.Reader(buf)
	// b, err := ioutil.ReadAll(reader)
	// if err != nil {
	// 	panic(err)
	// }
	// sss := string(b)

	// lex := *NewLexer(sss)
	lex := *NewLexer(filename)

	c := NewCMMS("root")
	c.ParseMetaData(lex)

	return *c
}

func GetCMMS(filename string) CMMS {

	var data []byte
	var ret CMMS

	//	file, _ := os.Open("test/1Cv7.MD")
	file, _ := os.Open(filename)
	defer file.Close()
	doc, err := mscfb.New(file)
	if err != nil {
		return ret
	}

	for entry, err := doc.Next(); err == nil; entry, err = doc.Next() {
		if entry.Name == "Main MetaData Stream" {
			btStream := make([]byte, entry.Size)
			_, er := entry.Read(btStream)
			if er != nil {
				log.Fatal(err)
			}
			i := 0
			for i = 0; i < len(btStream); i++ {
				if btStream[i] == '{' {
					break
				}
			}
			if (i > 0) && (i < len(btStream)) {
				btStream = btStream[i:]
			}

			decoder := charmap.Windows1251.NewDecoder()
			buf := bytes.NewBuffer([]byte{})
			buf.Write(btStream)

			reader := decoder.Reader(buf)
			b, err := ioutil.ReadAll(reader)
			if err != nil {
				panic(err)
			}
			sss := string(b)

			file, _err := os.Create(filename + ".MDP")
			if _err != nil {
				fmt.Println("Unable to create file:", _err)
				os.Exit(1)
			}
			defer file.Close()
			file.WriteString(sss)
			//file.Write(btStream)

			lex := *NewLexer(sss)

			c := NewCMMS("root")
			c.ParseMetaData(lex)
			//c.PrintLog(0)
			data, err = json.Marshal(c)
			//FileMDP := t.fileMetadata + ".cache"
			file, _err = os.Create(filename + ".cache")
			if _err != nil {
				fmt.Println("Unable to create file:", err)
				os.Exit(1)
			}
			defer file.Close()
			file.Write(data)

			ret = *c
		}
	}
	/*
		stg := StgOpenStorage(filename)
		if stg != nil {

			var i int

			metadata := stg.OpenStorage("Metadata")
			if metadata != nil {
				//fmt.Print("!")
				stream := metadata.OpenStream("Main MetaData Stream")
				lSize := stream.GetSize()
				//fmt.Printf("lSize=%d\n", lSize)

				btStream := make([]byte, lSize)
				btStream = stream.Read(btStream, lSize)
				for i = 0; i < len(btStream); i++ {
					if btStream[i] == '{' {
						break
					}
				}
				if (i > 0) && (i < len(btStream)) {
					btStream = btStream[i:]
				}
				//fmt.Printf("sz=%d\n", len(btStream))

				decoder := charmap.Windows1251.NewDecoder()
				buf := bytes.NewBuffer([]byte{})
				buf.Write(btStream)

				reader := decoder.Reader(buf)
				b, err := ioutil.ReadAll(reader)
				if err != nil {
					panic(err)
				}
				sss := string(b)
				//fmt.Printf("sz=%d\n", len(sss))

				file, _err := os.Create(filename + ".MDP")
				if _err != nil {
					fmt.Println("Unable to create file:", _err)
					os.Exit(1)
				}
				defer file.Close()
				file.WriteString(sss)
				//file.Write(btStream)

				lex := *NewLexer(sss)

				c := NewCMMS("root")
				c.ParseMetaData(lex)
				//c.PrintLog(0)
				data, err = json.Marshal(c)
				//FileMDP := t.fileMetadata + ".cache"
				file, _err = os.Create(filename + ".cache")
				if _err != nil {
					fmt.Println("Unable to create file:", err)
					os.Exit(1)
				}
				defer file.Close()
				file.Write(data)

				ret = *c
			}
		}
	*/
	return ret
}

type TableType struct {
	Alias string
	Tip   string
	Vid   string
}

type MetaDataWork struct {
	fileMetadata string
	strMetaData  string

	//{
	templParam string
	//}

	c                                         CMMS
	ConnectInfo                               ParseDBA.ConnectInfo
	commonProp                                MDRecCol
	sprav, consts, enumList, docList, regList MDRecCol

	DataTA         time.Time
	timeTA         int64
	PositionTA     string
	DocumetTA      string //ДокументТА
	DateTimeIddoc  string //ДатаВремяИДДок
	BorderCalcReg  string //ГраницаРасчетаРегистра
	TimeOfRegister string //ВремяРасчетаРегистра
	Snap           string

	QuartMonth []int

	SubQuery []string // Сгенерированные подзапросы, которые нужно добавить перед Query

	Param map[string]interface{}

	TableOfType map[string]TableType //[]TableType

	ObjectsByID    map[string]MDObject
	ObjectsByDescr map[string]MDObject
}

func (t *MetaDataWork) GetDateTimeIdocTA() string {
	v := ""

	v = fmt.Sprintf("%s%6s%s", t.DataTA.Format("20060102"), strconv.FormatInt(t.timeTA, 36), t.DocumetTA)

	return v
}

func (t *MetaDataWork) CalculateBoundariesTA() {

	if t.ConnectInfo.Server == "" {
		return
	}
	connString := t.GetConnectString()

	var db *sql.DB
	var rows *sql.Rows
	var err error
	db, err = sql.Open("sqlserver", connString)
	if err != nil {
		fmt.Printf("Error creating connection pool: %s\n", err.Error())
		return
	}
	defer db.Close()

	if len(t.QuartMonth) == 0 {
		t.QuartMonth = append(t.QuartMonth, 1)
		t.QuartMonth = append(t.QuartMonth, 4)
		t.QuartMonth = append(t.QuartMonth, 7)
		t.QuartMonth = append(t.QuartMonth, 10)
	}

	ctx := context.Background()
	err = db.PingContext(ctx)
	if err != nil {
		fmt.Println(err.Error())
	}

	rows, err = db.QueryContext(ctx, "SELECT [CURDATE],[CURTIME],[EVENTIDTA], [SNAPSHPER] FROM [_1SSYSTEM]")
	if err != nil {
		fmt.Printf("Error SELECT FROM _1SSYSTEM : %s\n", err.Error())
		return
	}
	// Iterate through the result set.
	for rows.Next() {
		//var _timeTA int64
		err = rows.Scan(&t.DataTA, &t.timeTA, &t.DocumetTA, &t.Snap)
		t.PositionTA = fmt.Sprintf("%s%10d%10s", t.DataTA.Format("20060102"), t.timeTA, t.DocumetTA)
	}

	t.DateTimeIddoc = t.GetDateTimeIdocTA()
	t.BorderCalcReg = t.DateTimeIddoc[:8]
	t.TimeOfRegister = t.DateTimeIddoc[8:]

	//fmt.Printf("%s %s\n", t.DataTA.Format("20060102"), t.DateTimeIddoc)
}

func (t MetaDataWork) GetConstantaMetaProp(name string) _MDRec {
	var r ConstRec
	r = t.GetConstantaByName(name)
	if r.ID == 0 {
		var m _MDRec
		return m
	}

	return r._MDRec
}

func (t MetaDataWork) GetSpravMetaProp(name string, mRekv string) _MDRec {
	r := t.GetSpravByName(name)
	m := r.GetRekvByName(mRekv)
	if m.ID == 0 {
		var mr _MDRec
		return mr
	}

	return m._MDRec
}

func (t MetaDataWork) GetEnumValMetaProp(name string, mRekv string) _MDRec {
	r := t.GetEnumByName(name)
	if r.ID == 0 {
		var mr _MDRec
		return mr
	}
	ss := "ПЕРЕЧИСЛЕНИЕ." + name + "." + mRekv
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		_obj := val.obj
		switch obj := _obj.(type) {
		case EnumVal:
			return obj._MDRec
		}
	}

	var mr _MDRec
	return mr
}

func (t MetaDataWork) GetDocumentMetaProp(name string, mRekv string) _MDRec {
	r := t.GetDocByName(name)
	if r.ID == 0 {
		var mr _MDRec
		return mr
	}
	ss := "ДОКУМЕНТ." + name + "." + mRekv
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		_obj := val.obj
		switch obj := _obj.(type) {
		case DocHead:
			return obj._MDRec
		case DocTable:
			return obj._MDRec
		}
	}

	var mr _MDRec
	return mr
}

func (t MetaDataWork) GetRegistrMetaProp(name string, mRekv string) _MDRec {
	r := t.GetRegistrByName(name)
	if r.ID == 0 {
		var mr _MDRec
		return mr
	}
	//	return t.GetRegistrMetaProp(name, mRekv)

	//var mr _MDRec
	//mr = t.GetRegistrMetaProp(name,mRekv)
	ss := "РЕГИСТР." + name + "." + mRekv
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		_obj := val.obj
		switch obj := _obj.(type) {
		case RegIzm:
			return obj._MDRec
		case RegReq:
			return obj._MDRec
		case RegRes:
			return obj._MDRec
		}
	}

	var mr _MDRec
	return mr
}

func (t MetaDataWork) GetCommonPropByName(name string) CommonProp {
	ss := "ОбщийРеквизит." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		_obj := val.obj
		switch obj := _obj.(type) {
		case CommonProp:
			return obj
		}
	}

	var r CommonProp
	return r
}

func (t MetaDataWork) GetConstantaByName(name string) ConstRec {
	ss := "Константа." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case ConstRec:
			return obj
		}
	}

	var r ConstRec
	return r
}

func (t MetaDataWork) GetConstantaById(ID int) ConstRec {
	ss := IntToString(ID)
	if val, ok := t.ObjectsByID[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case ConstRec:
			return obj
		}
	}

	var r ConstRec
	return r
}

func (t MetaDataWork) GetSpravByName(name string) SpravRec {
	ss := "Справочник." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case SpravRec:
			return obj
		}
	}

	var r SpravRec
	return r
}

func (t MetaDataWork) GetSpravByID(ID int) SpravRec {
	ss := IntToString(ID)
	if val, ok := t.ObjectsByID[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case SpravRec:
			return obj
		}
	}

	var r SpravRec
	return r
}

func (t MetaDataWork) GetRegistrByName(name string) RegRec {
	ss := "Регистр." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case RegRec:
			return obj
		}
	}

	var r RegRec
	return r
}

func (t MetaDataWork) GetRegistrByID(ID int) RegRec {
	ss := IntToString(ID)
	if val, ok := t.ObjectsByID[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case RegRec:
			return obj
		}
	}

	var r RegRec
	return r
}

func (t MetaDataWork) GetDocByName(name string) DocRec {
	ss := "Документ." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case DocRec:
			return obj
		}
	}

	var r DocRec
	return r
}

func (t MetaDataWork) GetDocByID(ID int) DocRec {
	ss := IntToString(ID)
	if val, ok := t.ObjectsByID[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case DocRec:
			return obj
		}
	}

	var r DocRec
	return r
}

func (t MetaDataWork) GetEnumByName(name string) EnumRec {
	ss := "Перечисление." + name
	if val, ok := t.ObjectsByDescr[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case EnumRec:
			return obj
		}
	}

	var r EnumRec
	return r
}

func (t MetaDataWork) GetEnumByID(ID int) EnumRec {
	ss := IntToString(ID)
	if val, ok := t.ObjectsByID[strings.ToUpper(ss)]; ok {
		//return t.consts.RecMD[val]
		_obj := val.obj
		switch obj := _obj.(type) {
		case EnumRec:
			return obj
		}
	}

	var r EnumRec
	return r
}

func (t MetaDataWork) GetStringParam(i int) string {
	strTempl := ""
	for k := 1; k < i; k++ {
		strTempl = strTempl + "(" + t.templParam + ",)?"
	}
	strTempl = strTempl + "(" + t.templParam + ")?\\)"

	return strTempl

}

func (t MetaDataWork) PrepareParameter(v string) string {
	v = strings.Replace(v, ",", "", -1)

	return strings.Trim(v, " ")
}

func (t MetaDataWork) GetStringFromDate(tTime time.Time) string {
	return fmt.Sprintf("%s", tTime.Format("20060102"))
}

func (t *MetaDataWork) AddParam(n string, v interface{}) {
	t.Param[n] = v
}

type PeriodBoundaries struct {
	active   int
	data     time.Time
	border   string
	Time     string
	value    interface{}
	position string
}

func (t MetaDataWork) SelectVariable(v string) string {
	v = strings.Replace(v, ":", "", -1)
	v = strings.Replace(v, "~", "", -1)
	v = strings.Replace(v, "*", "", -1)

	return v
}

// func (t MetaDataWork) LongToCharID36(ID int64, val string, Len int) string {
func (t MetaDataWork) LongToCharID36(ID int64, Len int) string {

	Buffer := ""
	for i := 0; i < Len; i++ {
		Buffer = Buffer + " "
	}
	str := strings.ToUpper(strconv.FormatInt(ID, 36))
	Start := Len - len(str)
	Buffer = Buffer[:Start]
	j := 0
	nLen := len(str)
	if Len <= len(str) {
		nLen = len(str)
	}
	for i := Start; i < (Start + nLen); i++ {
		if j == len(str) {
			break
		}
		Buffer = Buffer + string(str[j])
		j++
	}

	return Buffer
}

func (t MetaDataWork) PrepareBoundaryPeriod(v string) PeriodBoundaries { //ПодготовитьГраницыПериода
	var r PeriodBoundaries

	r.active = 0
	v = strings.Replace(v, ",", "", -1)
	if v[0] == ':' {
		VariableDateCalculation := t.SelectVariable(v)
		Modifier := 0
		if v[len(v)-1] == '~' {
			Modifier = 1
		}
		if val, ok := t.Param[VariableDateCalculation]; ok {
			switch obj := val.(type) {
			case time.Time:
				r.active = 1
				r.data = obj.AddDate(0, 0, Modifier)
				r.border = t.GetStringFromDate(r.data)
				r.Time = "     0     0   "
				r.position = ""
				r.value = obj

				//fmt.Printf("obj=%s r.data=%s", t.GetStringFromDate(obj), t.GetStringFromDate(r.data))

			default:
				fmt.Printf("Неверное значение параметра '%s' %T", VariableDateCalculation, obj)
			}
		} else {
			fmt.Printf("Неверное значение параметра '%s'", VariableDateCalculation)
		}
	}

	return r
}

func (t MetaDataWork) ParsingDataSources(src string) string {

	retStr := src

	Pattern := `(([^\wа-яА-Яё]*(FROM|JOIN|ИЗ|СОЕДИНЕНИЕ)[^\wа-яА-ЯёЁ#]+)\$(([\wа-яА-ЯЁё]+)[\.]*([\wа-яА-ЯЁё]*))[^\wа-яА-ЯЁё]+)`
	matched, err := regexp.Match("(?i)"+Pattern, []byte(src))
	if err != nil {
		fmt.Println(err.Error())
		os.Exit(1)
	}
	if !matched {
		return src
	}
	re := regexp.MustCompile("(?i)" + Pattern)
	retStr = src
	res := re.FindAllStringSubmatch(src, -1)
	for i := range res {
		KeyWord := res[i][4]
		VregDataType := strings.ToUpper(res[i][5])
		VidData := res[i][6]

		strRepl := "$" + KeyWord

		//fmt.Printf("KeyWord=%s VregDataType=%s VidData=%s\n", KeyWord, VregDataType, VidData)
		if VregDataType == "СПРАВОЧНИК" {
			strRepl = t.ReferenceTableName(VidData)
		} else if VregDataType == "ДОКУМЕНТ" {
			strRepl = t.DocHeadTableName(VidData)
		} else if VregDataType == "ДОКУМЕНТСТРОКИ" {
			strRepl = t.DocTableName(VidData)
		} else if VregDataType == "РЕГИСТР" {
			strRepl = t.TableNameRegMove(VidData)
		} else if VregDataType == "РЕГИСТРИТОГИ" {
			strRepl = t.TableNameRegItog(VidData)
		} else if VregDataType == "ЖУРНАЛДОКУМЕНТОВ" {
			strRepl = "_1SJOURN"
		} else if VregDataType == "ССЫЛКИДОКУМЕНТОВ" {
			strRepl = "_1SCRDOC"
		} else if VregDataType == "КОНСТАНТЫ" {
			strRepl = "_1SCONST"
		}

		retStr = strings.Replace(retStr, "$"+KeyWord, strRepl, -1)
	}

	return retStr
}

func (t *MetaDataWork) GetParametersExpressions(Pattern string, txt string) *regexp.Regexp {

	Pattern = "(?im)" + Pattern
	matched, err := regexp.Match("(?i)"+Pattern, []byte(txt))
	if err != nil {
		fmt.Println(err.Error())
		return nil
	}
	if !matched {
		return nil
	}

	re := regexp.MustCompile(Pattern)
	return re
}

func (t *MetaDataWork) FillTableOfSources(src string) {
	Pattern := `(?:из|from|соединение|join)[^\wа-яА-ЯЁё\(\[#\$]+\$([\wа-яА-ЯЁё]+)\.?([\wа-яА-ЯЁё]*)[^\wа-яА-ЯЁё]+(?:как|as)?[^\wа-яА-ЯЁё]*([\wа-яА-ЯЁё]*)[^\wа-яА-ЯЁё\,]`
	matched, err := regexp.Match("(?i)"+Pattern, []byte(src))
	if err != nil {
		fmt.Println(err.Error())
		return
	}
	if !matched {
		return
	}
	re := regexp.MustCompile("(?i)" + Pattern)
	//retStr := src
	res := re.FindAllStringSubmatch(src, -1)
	for i := range res {
		var v TableType
		v.Alias = res[i][3]
		v.Tip = res[i][1]
		v.Vid = res[i][2]
		//t.TableOfType = append(t.TableOfType, v)
		t.TableOfType[strings.ToUpper(v.Alias)] = v
		//fmt.Printf("%q\n", res[i])
	}

}

func (t MetaDataWork) ParsingPropsConstant(FirstPart string, TwoPart string) string {
	mc := t.GetConstantaByName(TwoPart)
	if mc.TypeObj == int(md_None) {
		return "$" + FirstPart + "." + TwoPart
	}
	val := t.PrepareValue(mc._MDRec, "const_vt")
	return "(SELECT " + val + "\n" +
		"FROM _1sconst as const_vt (NOLOCK)\n" +
		"WHERE const_vt.OBJID = '     0   '\n" +
		"AND const_vt.ID = " + IntToString(mc.ID) + ")"
}

func (t MetaDataWork) ParsingCommonProps(FirstPart string, TwoPart string) string {
	mc := t.GetCommonPropByName(TwoPart)
	if mc.TypeObj == int(md_None) {
		return "$" + FirstPart + "." + TwoPart
	}
	val := "sp" + IntToString(mc.ID)
	return val
}

func (t MetaDataWork) ParsingPropsReference(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ТЕКУЩИЙЭЛЕМЕНТ" {
		strChange = FirstPart + ".ID"
	} else if TwoPart == "НАИМЕНОВАНИЕ" {
		strChange = FirstPart + ".DESCR"
	} else if TwoPart == "КОД" {
		strChange = FirstPart + ".CODE"
	} else if TwoPart == "ПОМЕТКАУДАЛЕНИЯ" {
		strChange = "CASE WHEN " + FirstPart + ".ISMARK = 1 THEN 1 ELSE 0 END"
	} else if TwoPart == "ЭТОГРУППА" {
		strChange = "CASE WHEN " + FirstPart + ".ISFOLDER = 1 THEN 1 ELSE 0 END"
	} else if TwoPart == "РОДИТЕЛЬ" {
		strChange = FirstPart + ".PARENTID"
	} else if TwoPart == "ВЛАДЕЛЕЦ" {
		strChange = FirstPart + ".PARENTEXT"
	} else {
		ms := t.GetSpravByName(vidData)
		mr := ms.GetRekvByName(TwoPart)
		if mr.ID != 0 {
			strChange = FirstPart + ".SP" + IntToString(mr.ID)
		} else {
			strChange = "$" + FirstPart + "." + TwoPart
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingAttributesJournalDocuments(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ТЕКУЩИЙДОКУМЕНТ" {
		strChange = FirstPart + ".IDDOC"
	} else if TwoPart == "ВИДДОКУМЕНТА" {
		strChange = FirstPart + ".IDDOCDEF"
	} else if TwoPart == "ПОМЕТКАУДАЛЕНИЯ" {
		strChange = "CASE WHEN " + FirstPart + ".ISMARK = 1 THEN 1 ELSE 0 END"
	} else if TwoPart == "ПРОВЕДЕН" {
		strChange = FirstPart + ".CLOSED&1"
	} else if TwoPart == "ДАТАДОК" {
		strChange = "LEFT(" + FirstPart + ".DATE_TIME_IDDOC,8)"
	} else if TwoPart == "ВРЕМЯДОКУМЕНТА" {
		strChange = "dbo.ConvertIDTimeToTime(substring(" + FirstPart + ".date_time_iddoc,9,6))"
	} else if TwoPart == "НОМЕРДОК" {
		strChange = FirstPart + ".DOCNO"
	} else if TwoPart == "ЖУРНАЛ" {
		strChange = FirstPart + ".IDJOURNAL"
	} else if TwoPart == "ПРЕФИКС" {
		strChange = FirstPart + ".DNPREFIX"
	} else if TwoPart == "ПОЗИЦИЯДОКУМЕНТА" {
		strChange = FirstPart + ".DATE_TIME_IDDOC"
	} else {
		cr := t.GetCommonPropByName(TwoPart)
		if cr.TypeObj == int(md_None) {
			strChange = "$" + FirstPart + "." + TwoPart
		} else {
			strChange = FirstPart + ".SP" + IntToString(cr.ID)
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingAttributesDocument(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ТЕКУЩИЙДОКУМЕНТ" {
		strChange = FirstPart + ".IDDOC"
	} else {
		cr := t.GetDocByName(vidData)
		if cr.ID == 0 {
			strChange = "$" + FirstPart + "." + TwoPart
		} else {
			cc := cr.GetDocHeadByName(TwoPart)
			//if cc.TypeObj == int(md_None) {
			if cc.ID == 0 {
				ct := cr.GetDocTableByName(TwoPart)
				if ct.ID == 0 {
					strChange = "$" + FirstPart + "." + TwoPart
				} else {
					strChange = FirstPart + ".SP" + IntToString(ct.ID)
				}
			} else {
				strChange = FirstPart + ".SP" + IntToString(cc.ID)
			}
			//strChange = FirstPart + ".SP" + IntToString(cr.ID)
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingAttributesDocumentTable(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ТЕКУЩИЙДОКУМЕНТ" {
		strChange = FirstPart + ".IDDOC"
	} else if TwoPart == "НОМЕРСТРОКИ" {
		strChange = FirstPart + ".LINENO_"
	} else {
		cr := t.GetDocByName(vidData)
		//		if cr.TypeObj == int(md_None) {
		if cr.ID == 0 {
			strChange = "$" + FirstPart + "." + TwoPart
		} else {
			cc := cr.GetDocTableByName(TwoPart)
			if cc.ID == 0 {
				strChange = "$" + FirstPart + "." + TwoPart
			} else {
				strChange = FirstPart + ".SP" + IntToString(cc.ID)
			}
			//strChange = FirstPart + ".SP" + IntToString(cr.ID)
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingAttributesRegistr(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ТЕКУЩИЙДОКУМЕНТ" {
		strChange = FirstPart + ".IDDOC"
	} else if TwoPart == "НОМЕРСТРОКИ" {
		strChange = FirstPart + ".LINENO_"
	} else if TwoPart == "ВИДДВИЖЕНИЯ" {
		strChange = FirstPart + ".DEBKRED"
	} else if TwoPart == "ВИДДОКУМЕНТА" {
		strChange = FirstPart + ".IDDOCDEF"
	} else if TwoPart == "ДАТА" {
		strChange = "CAST(LEFT(" + FirstPart + ".DATE_TIME_IDDOC,8) AS DATETIME)"
	} else if TwoPart == "ВРЕМЯ" {
		strChange = "SUBSTRING(" + FirstPart + ".DATE_TIME_IDDOC,9,6)"
	} else if TwoPart == "ПОЗИЦИЯДОКУМЕНТА" {
		strChange = FirstPart + ".DATE_TIME_IDDOC"
	} else {
		cr := t.GetRegistrByName(vidData)
		if cr.ID == 0 {
			strChange = "$" + FirstPart + "." + TwoPart
		} else {
			cc := t.GetRegistrMetaProp(cr.SID, TwoPart) ////cr.GetDocHeadByName(TwoPart)
			if cc.ID == 0 {
				strChange = "$" + FirstPart + "." + TwoPart
			} else {
				strChange = FirstPart + ".SP" + IntToString(cc.ID)
			}
			//strChange = FirstPart + ".SP" + IntToString(cr.ID)
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingAttributesRegistrItog(FirstPart string, TwoPart string, vidData string) string {
	strChange := ""
	TwoPart = strings.ToUpper(TwoPart)
	if TwoPart == "ПЕРИОД" {
		strChange = FirstPart + ".PERIOD"
	} else {
		cr := t.GetRegistrByName(vidData)
		if cr.ID == 0 {
			strChange = "$" + FirstPart + "." + TwoPart
		} else {
			cc := t.GetRegistrMetaProp(cr.SID, TwoPart) ////cr.GetDocHeadByName(TwoPart)
			if cc.ID == 0 {
				strChange = "$" + FirstPart + "." + TwoPart
			} else {
				strChange = FirstPart + ".SP" + IntToString(cc.ID)
			}
			//strChange = FirstPart + ".SP" + IntToString(cr.ID)
		}
	}

	return strChange
}

func (t MetaDataWork) ParsingTableAttributes(v string) string {

	re := t.GetParametersExpressions(`(?:\[[^\]]*\])|(\$([\wа-яё]+)\.*([\wа-яё]*))[^\wа-яё'"\$]+`, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {
		strChange := ""
		KeyWord := res[i][1]
		FirstPart := res[i][2]
		TwoPart := res[i][3]
		if FirstPart == "" {
			strChange = KeyWord
		} else if strings.ToUpper(FirstPart) == "КОНСТАНТА" {
			strChange = t.ParsingPropsConstant(FirstPart, TwoPart)
		} else if strings.ToUpper(FirstPart) == "ОБЩИЙРЕКВИЗИТ" {
			strChange = t.ParsingPropsConstant(FirstPart, TwoPart)
		} else {
			tt := t.TableOfType[strings.ToUpper(FirstPart)]
			if tt.Alias == "" {
				continue
			}
			tipData := tt.Tip
			vidData := tt.Vid
			tipDataUpper := strings.ToUpper(tipData)
			if tipDataUpper == "СПРАВОЧНИК" {
				strChange = t.ParsingPropsReference(FirstPart, TwoPart, vidData)
			} else if tipDataUpper == "ЖУРНАЛДОКУМЕНТОВ" {
				strChange = t.ParsingAttributesJournalDocuments(FirstPart, TwoPart, vidData)
			} else if tipDataUpper == "ДОКУМЕНТ" {
				strChange = t.ParsingAttributesDocument(FirstPart, TwoPart, vidData)
			} else if tipDataUpper == "ДОКУМЕНТСТРОКИ" {
				strChange = t.ParsingAttributesDocumentTable(FirstPart, TwoPart, vidData)
			} else if tipDataUpper == "РЕГИСТР" {
				strChange = t.ParsingAttributesRegistr(FirstPart, TwoPart, vidData)
			} else if tipDataUpper == "РЕГИСТРИТОГИ" {
				strChange = t.ParsingAttributesRegistrItog(FirstPart, TwoPart, vidData)
			}
			//fmt.Printf("FirstPart=%s tipDataUpper=%s vidData=%s\n", FirstPart, tipDataUpper, vidData)
		}
		//fmt.Printf("strChange=%s TwoPart=%s\n", strChange, TwoPart)
		v = strings.Replace(v, KeyWord, strChange, -1)
	}

	return v
}

func (t MetaDataWork) FindModificator(v string) int {
	Modificator := 0
	if v == "*" {
		Modificator = -1
	}
	for i := 0; i < len(v); i++ {
		if v[i] == '~' {
			Modificator++
		}
	}

	return Modificator
}

func (t MetaDataWork) ParseParameters(v string) string {
	//	re := t.GetParametersExpressions(`(?:\:)+([a-zа-яё]{1}[\wа-яё]*(~|\*)*)`, v)
	re := t.GetParametersExpressions(`'[^']*'|"[^"]*"|\[[^\]]*\]|(\:((?:[\wа-яё]+\.?)+)(~|\*)*)`, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {
		VariableCalculation := t.SelectVariable(res[i][2])
		//Modificator := res[i][2]
		Modifier := t.FindModificator(res[i][2])

		FirstPart := ""
		SecondPart := ""
		ThridPart := ""
		if strings.Contains(VariableCalculation, ".") {
			listParametr := strings.Split(VariableCalculation, ".")
			FirstPart = listParametr[0]
			SecondPart = listParametr[1]
			if len(listParametr) > 2 {
				ThridPart = listParametr[2]
			}
		} else {
			FirstPart = VariableCalculation
		}

		//fmt.Printf("FirstPart=%s SecondPart=%s ThridPart=%s\n", FirstPart, SecondPart, ThridPart)

		switch strings.ToUpper(FirstPart) {
		case "ВИДДОКУМЕНТА":
			md := t.GetDocByName(SecondPart)
			strValue := IntToString(md.ID)
			if Modifier == 1 {
				strValue = "'" + t.LongToCharID36(int64(md.ID), 4) + "'"
			}
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ВИДПЕРЕЧИСЛЕНИЯ":
			md := t.GetEnumByName(SecondPart)
			strValue := IntToString(md.ID)
			if Modifier == 1 {
				strValue = "'" + t.LongToCharID36(int64(md.ID), 4) + "'"
			}
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ВИДСПРАВОЧНИКА":
			md := t.GetSpravByName(SecondPart)
			strValue := IntToString(md.ID)
			if Modifier == 1 {
				strValue = "'" + t.LongToCharID36(int64(md.ID), 4) + "'"
			}
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ПЕРЕЧИСЛЕНИЕ":
			et := t.GetEnumByName(SecondPart)
			ev := t.GetEnumValMetaProp(SecondPart, ThridPart)
			strValue := "'"
			if Modifier == 1 {
				strValue = "'E1"
				strValue = strValue + t.LongToCharID36(int64(et.ID), 4)
			}
			strValue = strValue + t.LongToCharID36(int64(ev.ID), 6) + "'"
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ПУСТОЙИД":
			strValue := "'     0   '"
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ПУСТОЙИД13":
			strValue := "'   0     0   '"
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ПУСТАЯДАТА":
			strValue := "'17530101'"
			v = strings.Replace(v, res[i][0], strValue, -1)
		case "ТИП":
			switch strings.ToUpper(SecondPart) {
			case "ДОКУМЕНТ":
				strValue := "'O1'"
				v = strings.Replace(v, res[i][0], strValue, -1)
			case "СПРАВОЧНИК":
				strValue := "'B1'"
				v = strings.Replace(v, res[i][0], strValue, -1)
			case "ПЕРЕЧИСЛЕНИЕ":
				strValue := "'E1'"
				v = strings.Replace(v, res[i][0], strValue, -1)
			}
		default:
			if val, ok := t.Param[VariableCalculation]; ok {
				strValue := ""
				switch obj := val.(type) {
				case time.Time:
					if Modifier == 0 {
						strValue = "'" + obj.Format("20060102") + "'"
					} else if Modifier == 1 {
						strValue = "'" + obj.Format("20060102") + "Z'"
					} else if Modifier == 2 {
						strValue = fmt.Sprintf("{d '%04d-%02d-%02d'}", obj.Year(), obj.Month(), obj.Day())
					}
				case string:
					strValue = "'" + strings.ReplaceAll(obj, "'", "''") + "'"
				case int, int16, int32, int64:
					strValue = fmt.Sprintf("%d", obj)
				case uint, uint16, uint32, uint64:
					strValue = fmt.Sprintf("%d", obj)
				case float32, float64:
					strValue = fmt.Sprintf("%f", obj)
				default:
					strValue = fmt.Sprintf("%q", obj) //res[i][0]
				}
				v = strings.Replace(v, res[i][0], strValue, -1)
			}
		}

		//fmt.Printf("%d %q\n", i, res[i])
	}

	return v
}

func TypePeriodFromChar(ch string) PeriodType {
	switch ch {
	case "F":
		return eFiveDays //  5 дней
	case "C":
		return eTenDays //  Декада (10 дней)
	case "T":
		return eFifteenDays //  15 дней
	case "M":
		return eMonth //  год
	case "Y":
		return eMonth //  месяц
	case "Q":
		return eQuart //  квартал
	case "W":
		return eWeek //  неделя
	case "D":
		return eDay //  день
	}

	return e_NotUsed
}

func (t MetaDataWork) CheckBordersRegister(tt *PeriodBoundaries) {
	BorderOutsideTA := 0 // ГраницаЗаПределамиТА
	//typeVal := fmt.Sprintf("%T", tt.value)
	switch obj := tt.value.(type) {
	case time.Time:
		if t.PositionTA < tt.position {
			tt.position = fmt.Sprintf("%T", obj)
			BorderOutsideTA = 1
		}
	default:
		if tt.data.After(t.DataTA) {
			BorderOutsideTA = 1
		}
	}
	if BorderOutsideTA == 1 {
		tt.data = t.DataTA.AddDate(0, 0, 1)
		tt.border = t.BorderCalcReg
		tt.Time = t.TimeOfRegister
		tt.value = t.DataTA.AddDate(0, 0, 1)
		tt.position = ""
	}
}

func (t MetaDataWork) GetBegOfPeriod(Date time.Time) time.Time {
	Year := Date.Year()
	Month := Date.Month()
	Day := Date.Day()
	DayOfWeek := int(Date.Weekday())
	//DayOfYear := Date.YearDay()

	dt := time.Date(Year, Month, Day, Date.Hour(), Date.Minute(), Date.Second(), Date.Nanosecond(), Date.Location())
	switch TypePeriodFromChar(t.Snap) {
	case eWeek:
		n := DayOfWeek - 1
		dt = Date.AddDate(0, 0, -n)
	case eMonth:
		dt = time.Date(Year, Month, 1, 0, 0, 0, 0, Date.Location())
	case eQuart:
		var n int = int(Month) / 4
		dt = time.Date(Year, time.Month(t.QuartMonth[n]), 1, 0, 0, 0, 0, Date.Location())
	case eYear:
		dt = time.Date(Year, time.Month(1), 1, 0, 0, 0, 0, Date.Location())
	case eTenDays:
		var n int = Day / 10
		dt = time.Date(Year, Month, (n*10 + 1), 0, 0, 0, 0, Date.Location())
	}

	return dt
}

func (t MetaDataWork) GetEndOfPeriod(Date time.Time) time.Time {
	Year := Date.Year()
	Month := Date.Month()
	Day := Date.Day()
	DayOfWeek := int(Date.Weekday())
	//DayOfYear := Date.YearDay()

	dt := time.Date(Year, Month, Day, Date.Hour(), Date.Minute(), Date.Second(), Date.Nanosecond(), Date.Location())
	switch TypePeriodFromChar(t.Snap) {
	case eWeek:
		n := 7 - DayOfWeek
		dt = Date.AddDate(0, 0, n)
	case eMonth:
		if int(Month) == 12 {
			dt = time.Date(Year+1, time.Month(1), 1, 0, 0, 0, 0, Date.Location())
		} else {
			dt = time.Date(Year+1, time.Month(int(Month)+1), 1, 0, 0, 0, 0, Date.Location())
		}
		dt = dt.AddDate(0, 0, -1)
	case eQuart:
		var n int = int(Month)/4 + 1
		if n < 5 {
			dt = time.Date(Year, time.Month(t.QuartMonth[n]), 1, 0, 0, 0, 0, Date.Location())
		} else {
			dt = time.Date(Year+1, time.Month(1), 1, 0, 0, 0, 0, Date.Location())
		}
		dt = dt.AddDate(0, 0, -1)
	case eYear:
		dt = time.Date(Year, time.Month(12), 31, 0, 0, 0, 0, Date.Location())
	case eTenDays:
		var n int = Day / 10
		dt = time.Date(Year, Month, (n*10 + 1), 0, 0, 0, 0, Date.Location())
	}

	return dt
}

// ПодготовитьУсловиеПоРегистрам
func (t MetaDataWork) PrepareConditionRegistr(condition string, RegistID string, nameTable string) string {
	if condition[len(condition)-1] == ',' {
		condition = condition[:len(condition)-1]
	}
	txtQuery := condition
	nameIzm := ""
	regRec := t.GetRegistrByName(RegistID)
	for i := 0; i < len(regRec.Izm.RecMD); i++ {
		sep := "|"
		if i == 0 {
			sep = ""
		}
		val := regRec.Izm.RecMD[i]
		switch obj := val.(type) {
		case RegIzm:
			nameIzm = nameIzm + sep + obj.SID
		}
	}
	re := t.GetParametersExpressions(`'[^']*'|"[^"]*"|(?:^|\s|[^\wа-яё\.]+)(`+nameIzm+`)[^\wа-яё'"]+`, condition)
	if re == nil {
		return txtQuery
	}
	res := re.FindAllStringSubmatch(condition, -1)
	for i := range res {
		keyWord := res[i][1]
		md := t.GetRegistrMetaProp(RegistID, keyWord)
		if md.ID == 0 {
			continue
		}
		strChange := nameTable + ".sp" + IntToString(md.ID)
		txtQuery = strings.Replace(txtQuery, keyWord, strChange, -1)
		//fmt.Printf("%d) %q", i, res[i])
	}
	return txtQuery
}

// Остатки_РегистрОстатки_SQL
func (t MetaDataWork) RegistrRests(res []string) string {
	txtQuery := ""
	RegistID := res[1]
	EndPeriod := res[2]
	Join := res[3]
	Compare := res[4]
	Izm := res[5]
	Resurs := res[6]

	regRec := t.GetRegistrByName(RegistID)
	nameRegistrMove := "ra_" + IntToString(regRec.ID)
	nameRegistrItog := "rg_" + IntToString(regRec.ID)

	nameTableMove := "RA" + IntToString(regRec.ID)
	nameTableItog := "RG" + IntToString(regRec.ID)

	var dataCalc time.Time
	var BorderCalc, TimeCalc, BorderTabItog string
	var HalfPeriod int

	UseTabMove := 0
	beginBorderMove := ""
	beginTimeMove := ""
	endBorderMove := ""
	endTimeMove := ""

	//{ подготовка 1-го параметра - КОНЕЦПЕРИОДА
	if strings.Trim(EndPeriod, " ") == "," {
		dataCalc = t.DataTA.AddDate(0, 0, 1)
		BorderCalc = t.BorderCalcReg
		TimeCalc = t.TimeOfRegister
		//valBorderCalc = dataCalc
	} else {
		tt := t.PrepareBoundaryPeriod(EndPeriod)
		if tt.active == 0 {
			return ""
		}
		t.CheckBordersRegister(&tt)
		dataCalc = tt.data
		BorderCalc = tt.border
		TimeCalc = tt.Time
		//valBorderCalc = dataCalc
	}
	if dataCalc.After(t.DataTA) {
		BorderTabItog = t.GetStringFromDate(t.GetBegOfPeriod(t.DataTA))
	} else {
		BeginPeriod := t.GetBegOfPeriod(dataCalc)
		EndPeriod := t.GetEndOfPeriod(dataCalc).AddDate(0, 0, 1)
		DayPeriod := dataCalc.Day()
		if EndPeriod.After(t.DataTA) {
			HalfPeriod = int(t.DataTA.Sub(BeginPeriod)/(time.Hour*24))/2 + 1
		} else {
			HalfPeriod = int(EndPeriod.Sub(BeginPeriod)/(time.Hour*24))/2 + 1
		}
		if BeginPeriod.Before(dataCalc) {
			if DayPeriod < HalfPeriod {
				UseTabMove = 1
				beginBorderMove = t.GetStringFromDate(BeginPeriod)
				beginTimeMove = "     0     0   "
				endBorderMove = BorderCalc
				endTimeMove = TimeCalc
				BorderTabItog = t.GetStringFromDate(BeginPeriod.AddDate(0, 0, -1))
			} else {
				UseTabMove = 2
				beginBorderMove = BorderCalc
				beginTimeMove = TimeCalc
				if EndPeriod.After(t.DataTA) {
					endBorderMove = t.BorderCalcReg
					endTimeMove = t.TimeOfRegister
				} else {
					endBorderMove = t.GetStringFromDate(EndPeriod)
					endTimeMove = "     0     0   "
				}
				BorderTabItog = t.GetStringFromDate(BeginPeriod)
			}
		} else {
			BorderTabItog = t.GetStringFromDate(BeginPeriod.AddDate(0, 0, -1))
		}
	}
	//}

	//{ подготовка 4-го параметра - ИЗМЕРЕНИЯ
	Izm = strings.Replace(Izm, "(", "", -1)
	Izm = strings.Replace(Izm, ")", "", -1)
	//Izm = strings.Replace(Izm, ",", "", -1)
	if Izm[len(Izm)-1] == ',' {
		Izm = Izm[:len(Izm)-1]
	}
	listIzm := strings.Split(Izm, ",")
	if len(listIzm) == 0 {
		allIzm := len(regRec.Izm.RecMD)
		for i := 0; i < allIzm; i++ {
			val := regRec.Izm.RecMD[i]
			switch obj := val.(type) {
			case RegIzm:
				listIzm = append(listIzm, obj.SID)
			}
		}
	}
	strIzmItog := ""
	strIzmRegistrItog := ""
	strIzmRegistrMove := ""
	for i := 0; i < len(listIzm); i++ {
		IzmID := listIzm[i]
		sep := "\n,"
		if i == (len(listIzm) - 1) {
			sep = ""
		}
		nameFieldTable := "sp" + IntToString(t.GetRegistrMetaProp(RegistID, IzmID).ID)
		strIzmItog = strIzmItog + IzmID + sep
		strIzmRegistrItog = strIzmRegistrItog + "totalreg." + nameFieldTable + " AS " + IzmID + sep
		strIzmRegistrMove = strIzmRegistrMove + "accumreg." + nameFieldTable + " AS " + IzmID + sep
	}
	//}

	//{ подготовка 5-го параметра - РЕСУРСЫ
	Resurs = strings.Replace(Resurs, "(", "", -1)
	Resurs = strings.Replace(Resurs, ")", "", -1)
	//Resurs = strings.Replace(Resurs, ",", "", -1)
	if Resurs[len(Resurs)-1] == ',' {
		Resurs = Resurs[:len(Resurs)-1]
	}
	listIzm = strings.Split(Resurs, ",")
	if len(listIzm) == 0 {
		allIzm := len(regRec.Resurs.RecMD)
		for i := 0; i < allIzm; i++ {
			val := regRec.Resurs.RecMD[i]
			switch obj := val.(type) {
			case RegIzm:
				listIzm = append(listIzm, obj.SID)
			}
		}
	}
	strResursItog := ""
	strResursRegistrItog := ""
	strResursRegistrMove := ""
	strResursHaving := ""
	for i := 0; i < len(listIzm); i++ {
		IzmID := listIzm[i]
		sep := ","
		if i == 0 {
			sep = ""
		}
		nameFieldTable := "sp" + IntToString(t.GetRegistrMetaProp(RegistID, IzmID).ID)
		strResursItog = strResursItog + sep + "SUM(" + IzmID + "Остаток) AS " + IzmID + "Остаток\n\t"
		strResursRegistrItog = strResursRegistrItog + sep + "totalreg." + nameFieldTable + " AS " + IzmID + "Остаток\n\t"
		ZnakEnd1 := ""
		if UseTabMove != 1 {
			ZnakEnd1 = "-"
		}
		ZnakEnd2 := ""
		if UseTabMove == 1 {
			ZnakEnd2 = "-"
		}
		strResursRegistrMove = strResursRegistrMove + sep + "CASE WHEN accumreg.debkred = 0 THEN " + ZnakEnd1 + "accumreg." + nameFieldTable + " ELSE " + ZnakEnd2 + "accumreg." + nameFieldTable + " END\n\t"
		sep = "OR "
		if i == 0 {
			sep = ""
		}
		strResursHaving = strResursHaving + sep + "(SUM(" + IzmID + "Остаток) <> 0)\n\t"
	}
	//}
	txtQuery = "	SELECT\n\t" + strIzmItog + "\n\t," + strResursItog + "\n\t" +
		"FROM \n\t (SELECT \n\t" + strIzmRegistrItog + "\n\t," + strResursRegistrItog + "\n\t" +
		" FROM \n\t " + nameTableItog + " AS totalreg (NOLOCK) \n\t"

	if Join != "," {
		txtQuery = txtQuery + t.PrepareConditionRegistr(Join, RegistID, "totalreg")
	}
	txtQuery = txtQuery + "\nWHERE\n\t totalreg.PERIOD = '" + BorderTabItog + "'\n\t"
	if Compare != "," {
		_Condition := t.PrepareConditionRegistr(Compare, RegistID, "totalreg")
		txtQuery = txtQuery + " AND \n\t " + _Condition

		//_Condition = fmt.Sprintf("valBorderCalc=%q beginBorderMove%q beginTimeMove=%q endBorderMove=%q endTimeMove=%q", valBorderCalc, beginBorderMove, beginTimeMove, endBorderMove, endTimeMove)
	}

	if UseTabMove != 0 {
		txtQuery = txtQuery + "\n\tUNION ALL\n\tSELECT\n\t" +
			strIzmRegistrMove + "\n\t," + strResursRegistrMove +
			"\n\tFROM\n\t"

		strDataTable := ""

		if regRec.Fast == 1 { //МетаРегистр.БыстраяОбработкаДвижений = 1
			txtQuery = txtQuery + nameTableMove + " AS accumreg (NOLOCK)\n\t"
			strDataTable = "accumreg.DATE_TIME_IDDOC"
		} else {
			txtQuery = txtQuery + "_1SJOURN AS docjourn (NOLOCK)\n\tLEFT JOIN " + nameTableMove + " AS accumreg (NOLOCK)\n\t" +
				"ON accumreg.IDDOC = docjourn.IDDOC\n\t"
			strDataTable = "docjourn.DATE_TIME_IDDOC"
		}
		if Join != "," {
			txtQuery = txtQuery + t.PrepareConditionRegistr(Join, RegistID, "accumreg")
		}
		keyWord := "\nWHERE"
		txtQuery = txtQuery + keyWord + " (" + strDataTable + " >= '" + beginBorderMove + beginTimeMove + "')\n\t" +
			"AND (" + strDataTable + " < '" + endBorderMove + endTimeMove + "')\n\t"
		keyWord = "\nAND"
		if Compare != "," {
			_Condition := t.PrepareConditionRegistr(Compare, RegistID, "accumreg")
			txtQuery = txtQuery + keyWord + "\n\t" + _Condition + "\n\t"
			keyWord = "\nAND"
		}
	}
	txtQuery = txtQuery + ") AS vt_totalreg\n\tGROUP BY\n\t\t" + strIzmItog + "\n\tHAVING " + strResursHaving + "\n\t"

	txtQuery = strings.Replace(txtQuery, "vt_totalreg", "vt_"+nameRegistrMove, -1)
	txtQuery = strings.Replace(txtQuery, "accumreg", "vt_"+nameRegistrMove, -1)
	txtQuery = strings.Replace(txtQuery, "totalreg", "vt_"+nameRegistrItog, -1)
	//fmt.Printf("EndPeriod=%s Join=%s Compare=%s Izm=%s Resurs=%s\n", EndPeriod, Join, Compare, Izm, Resurs)
	//fmt.Printf("nameRegistrMove=%s nameRegistrItog=%s nameTableMove=%s nameTableItog=%s\n", nameRegistrMove, nameRegistrItog, nameTableMove, nameTableItog)

	return "(\n" + txtQuery + "\n)"
}

// ПарсингВТРегистрОстатки
func (t MetaDataWork) ParsingVTRegisterBalances(v string) string {
	Param := t.GetStringParam(5)
	Pattern := `\$РегистрОстатки\.([\wа-яё]+[^\wа-яё\(]*)\(` + Param
	re := t.GetParametersExpressions(Pattern, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {

		strChange := t.RegistrRests(res[i])
		if strChange != "" {
			v = strings.Replace(v, res[i][0], strChange, -1)
		}

		//		fmt.Printf("%d %q\n", i, res[i])
	}

	return v
}

func PrepareString(s string) string {
	s = strings.Replace(s, "\n", "", -1)
	s = strings.Replace(s, "\t", " ", -1)
	if s[len(s)-1] == ',' {
		s = s[:len(s)-1]
	}

	return strings.Trim(s, " ")
}

// ПодготовитьУсловиеПоСрезПервыхПоследних
func (t *MetaDataWork) PrepareConditionBySliceFirstLast(strCondotion string, NameTable string) string {
	txtQuery := PrepareString(strCondotion)
	Pattern := `'[^']*'|\$?[\wа-я]+\.[\wа-я]+|[:@\$]?[\wа-я]+|[^:@\$\wа-я']+`
	re := t.GetParametersExpressions(Pattern, strCondotion)
	res := re.FindAllStringSubmatch(txtQuery, -1)
	for i := range res {
		keyWord := strings.Trim(res[i][0], " ")
		txtReplace := keyWord
		if strings.ToUpper(keyWord) == "ТЕКУЩИЙЭЛЕМЕНТ" {
			txtReplace = NameTable + ".objid"
		}
		txtReplace = strings.Replace(txtReplace, keyWord, txtReplace, -1)
		txtQuery = strings.Replace(txtQuery, keyWord, txtReplace, -1)
	}
	return txtQuery
}

func CreateFunctionIntToTime(db *sql.DB) error {
	var rows *sql.Rows

	ctx := context.Background()
	err := db.PingContext(ctx)
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}
	rows, err = db.QueryContext(ctx, "select name from dbo.sysobjects (nolock) where id = object_id(N'[dbo].[IntToTime]')")
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}
	if rows.Next() {
		return nil
	}

	_, err = db.ExecContext(ctx, `
	CREATE function [dbo].[IntToTime](@Deci int)
	returns char(9) as 
	begin
		return(right('0'+cast(floor(@Deci/36000000.0) as varchar(2)),2)+':'+right('0'+cast(floor((@Deci%36000000)/600000.0) as varchar(2)),2)+':'+right('0'+cast((@Deci%36000000)%600000/10000 as varchar(2)),2))
	end	`)
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}

	return nil
}

func CreateFunctionStrToId(db *sql.DB) error {
	var rows *sql.Rows
	ctx := context.Background()
	err := db.PingContext(ctx)
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}
	rows, err = db.QueryContext(ctx, "select name from dbo.sysobjects (nolock) where id = object_id(N'[dbo].[StrToId]')")
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}
	if rows.Next() {
		return nil
	}

	_, err = db.ExecContext(ctx, "create function StrToID(@Res36 char(9))\n"+
		"	returns int as \n"+
		"	begin\n"+
		"		declare @j int\n"+
		"		declare @Deci int\n"+
		"		DECLARE @Arr36 char(36)\n"+
		"		select @Arr36 = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'\n"+
		"		select @Deci = 0\n"+
		"		select @j = 1\n"+
		"		while @j <= len(ltrim(rtrim(@Res36)))\n"+
		"		begin\n"+
		"		if @j <> 1\n"+
		"			select @Deci = @Deci*36\n"+
		"			select @Deci = @Deci + charindex(substring(ltrim(rtrim(@Res36)), @j,1),@Arr36) -1\n"+
		"			select @j = @j+1\n"+
		"		end\n"+
		"		return(@Deci)\n"+
		"	end\n")
	if err != nil {
		fmt.Printf("Error CreateFunctionStrToId %s", err.Error())
		return err
	}

	return nil
}

// СрезПоследних_DBF_SQL
func (t *MetaDataWork) SliceLast_DBF_SQL(res []string) string {
	txtQuery := ""

	var ExpandPeriods int
	var err error

	SpravID := res[1]
	BeginPeriod := res[2]
	ConditionRequisites := res[3]
	AdditionalConditions := res[4]
	Join := res[5]
	_ExpandPeriods := res[6]
	if strings.Trim(_ExpandPeriods, " ") == "," {
		ExpandPeriods = 0
	} else {
		ExpandPeriods, err = strconv.Atoi(strings.Trim(_ExpandPeriods, " "))
		if err != nil {
			ExpandPeriods = 0
		}
	}
	//regRec := t.GetRegistrByName(RegistID)
	spravRec := t.GetSpravByName(SpravID)
	//strConditionByAttributes := ""
	strConditionColumn := ""
	strConditionColumnsData := ""
	strConditionColumnsDoc := ""
	strConditionData := ""
	strGroupColumns := ""
	strAddCondition := ""
	strJoin := ""
	KeyWord := "\nwhere "
	NameTableSprav := "SC" + IntToString(spravRec.ID)
	//{ подготовка 1-го параметра КОНЕЦПЕРИОДА
	if strings.Trim(BeginPeriod, " ") != "," {
		tt := t.PrepareBoundaryPeriod(BeginPeriod)
		if tt.active == 0 {
			return ""
		}
		//DataEndCalc := tt.data
		BorderEndCalc := tt.border
		//TimeEndCalc := tt.Time
		//ValueBorderCalc := tt.value

		strConditionData = KeyWord + `tconst_1.date <= '` + BorderEndCalc + `'`
		KeyWord = "and "
	}
	//}

	//{ подготовка 2-го параметра РЕКВИЗИТЫ
	NameTempTable := "slicelast_" + NameTableSprav

	var listReqv []string = make([]string, 0)

	ModeEditData := 0
	ModeEditDocum := 0

	if ConditionRequisites[len(ConditionRequisites)-1] == ',' {
		ConditionRequisites = ConditionRequisites[:len(ConditionRequisites)-1]
	}

	ConditionRequisites = strings.Replace(ConditionRequisites, "(", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, ")", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\n", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\t", " ", -1)
	if strings.Trim(ConditionRequisites, " \t\n") != "" {
		listReqv = strings.Split(ConditionRequisites, ",")
	}

	allReqv := spravRec.GetRekvCount()
	for cntR := 0; cntR < allReqv; cntR++ {
		//for _, nameReqv := range listReqv {
		metaRekv := spravRec.GetRekvByNum(cntR)
		//metaRekv := spravRec.GetRekvByName(nameReqv)
		nameReqv := metaRekv.SID
		if len(listReqv) > 0 {
			if Find(listReqv, nameReqv) == len(listReqv) {
				continue
			}
		}
		if metaRekv.Period == 0 {
			continue
		}
		reqvID := IntToString(metaRekv.ID)
		if metaRekv.ChangeDoc == 1 {
			ModeEditDocum = ModeEditDocum + 1
			if ModeEditDocum == 1 {
				strConditionColumnsDoc = strConditionColumnsDoc + reqvID
			} else {
				strConditionColumnsDoc = strConditionColumnsDoc + "," + reqvID
			}
		} else {
			ModeEditData = ModeEditData + 1
			if ModeEditData == 1 {
				strConditionColumnsData = strConditionColumnsData + reqvID
			} else {
				strConditionColumnsData = strConditionColumnsData + "," + reqvID
			}
		}
		txtValue := t.PrepareValue(metaRekv._MDRec, "slicelast")
		strConditionColumn = strConditionColumn + ",case when slicelast.id = " + reqvID +
			" then " + txtValue + " end " + nameReqv + "\n	"
		strGroupColumns = strGroupColumns + ",max(vt_slicelast." + nameReqv + ") as " + nameReqv + "\n	"
	}
	if ModeEditData > 1 {
		strConditionColumnsData = KeyWord + "tconst_1.id in (" + strConditionColumnsData + ")"
	} else {
		strConditionColumnsData = KeyWord + "tconst_1.id = " + strConditionColumnsData
	}
	if ModeEditDocum > 1 {
		strConditionColumnsDoc = KeyWord + "tconst_1.id in (" + strConditionColumnsDoc + ")"
	} else {
		strConditionColumnsDoc = KeyWord + "tconst_1.id = " + strConditionColumnsDoc
	}
	KeyWord = " and "
	//}

	//{ подготовка 3-го параметра ДОПОЛНИТЕЛЬНЫЕ УСЛОВИЯ
	if strings.Trim(AdditionalConditions, " ") != "," {
		strAddCondition = " and "
	}
	strAddCondition = strAddCondition + t.PrepareConditionBySliceFirstLast(AdditionalConditions, "tconst_1")
	//}

	//{ подготовка 4-го параметра СОЕДИНЕНИЕ
	strJoin = "\n" + t.PrepareConditionBySliceFirstLast(Join, "tconst_1")
	//}

	tmpStr := ""
	if ExpandPeriods == 1 {
		tmpStr = ",vt_slicelast.Дата,vt_slicelast.Время,vt_slicelast.Документ"
	}

	txtQuery = txtQuery + `SELECT
	vt_slicelast.ТекущийЭлемент
	` + tmpStr + `
	` + strGroupColumns + `
	from (
		select
			slicelast.objid ТекущийЭлемент
			`
	if ExpandPeriods == 1 {
		txtQuery = txtQuery + `,slicelast.date Дата,slicelast.time Время,slicelast.docid Документ
			`
	}
	txtQuery = txtQuery + `
	` + strConditionColumn + `
			from (`
	if ModeEditData > 0 {
		txtQuery = txtQuery + `
		select tconst_2.objid, tconst_2.id, tconst_2.date, 0 time, '     0   ' docid, tconst_2.value
		from (
			select tconst_1.objid, tconst_1.id, max(tconst_1.date) date
			from _1SCONST tconst_1 (NOLOCK)
			` + strJoin + `
			` + strConditionData + `
			` + strConditionColumnsData + `
			` + strAddCondition + `
			group by tconst_1.id,  tconst_1.objid) slicelast1
		inner join _1SCONST tconst_2 (NOLOCK)
		on slicelast1.id = tconst_2.id
		and slicelast1.objid = tconst_2.objid
		and slicelast1.date = tconst_2.date`
	}

	if ModeEditDocum > 0 {
		if ModeEditData > 0 {
			txtQuery = txtQuery + `
			UNION ALL
			`
		}
		txtQuery = txtQuery + `
					select tconst_4.objid, tconst_4.id, tconst_4.date, tconst_4.time, tconst_4.docid, tconst_4.value
					from (
						select tconst_3.objid, tconst_3.id, tconst_3.date, tconst_3.time, max(tconst_3.docid) docid
						from (
							select tconst_2.objid, tconst_2.id, tconst_2.date, max(tconst_2.time) time
							from (
								select tconst_1.objid, tconst_1.id, max(tconst_1.date) date
								from _1SCONST tconst_1 (NOLOCK)
								` + strJoin + `
								` + strConditionData + `
								` + strConditionColumnsDoc + `
								` + strAddCondition + `
								group by tconst_1.id, tconst_1.objid) slicelast1
							inner join _1SCONST tconst_2 (NOLOCK)
							on slicelast1.id = tconst_2.id
							and slicelast1.objid = tconst_2.objid
							and slicelast1.date = tconst_2.date
							group by tconst_2.id, tconst_2.objid, tconst_2.date) slicelast2				
						inner join _1SCONST tconst_3 (NOLOCK)
						on slicelast2.id = tconst_3.id
						and slicelast2.objid = tconst_3.objid
						and slicelast2.date = tconst_3.date
						and slicelast2.time = tconst_3.time
						group by tconst_3.id, tconst_3.objid, tconst_3.date, tconst_3.time) slicelast3
					inner join _1SCONST tconst_4 (NOLOCK)
					on slicelast3.id = tconst_4.id
					and slicelast3.objid = tconst_4.objid
					and slicelast3.date = tconst_4.date
					and slicelast3.time = tconst_4.time
					and slicelast3.docid = tconst_4.docid
		`
	}
	txtQuery = txtQuery + `		) slicelast
	) vt_slicelast
	group by vt_slicelast.ТекущийЭлемент
	`
	if ExpandPeriods == 1 {
		txtQuery = txtQuery + `		,vt_slicelast.Дата,vt_slicelast.Время,vt_slicelast.Документ`
	}
	txtQuery = strings.Replace(txtQuery, "slicelast", NameTempTable, -1)

	txtQuery = "( " + txtQuery + " ) "

	return txtQuery
}

// СрезПервых_DBF_SQL
func (t *MetaDataWork) SliceFirst_DBF_SQL(res []string) string {
	txtQuery := ""

	var ExpandPeriods int
	var err error

	SpravID := res[1]
	BeginPeriod := res[2]
	ConditionRequisites := res[3]
	AdditionalConditions := res[4]
	Join := res[5]
	_ExpandPeriods := res[6]
	if strings.Trim(_ExpandPeriods, " ") == "," {
		ExpandPeriods = 0
	} else {
		ExpandPeriods, err = strconv.Atoi(strings.Trim(_ExpandPeriods, " "))
		if err != nil {
			ExpandPeriods = 0
		}
	}
	spravRec := t.GetSpravByName(SpravID)
	//strConditionByAttributes := ""
	strConditionColumn := ""
	strConditionColumnsData := ""
	strConditionColumnsDoc := ""
	strConditionData := ""
	strGroupColumns := ""
	strAddCondition := ""
	strJoin := ""
	KeyWord := "\nwhere "
	NameTableSprav := "SC" + IntToString(spravRec.ID)
	//{ подготовка 1-го параметра НАЧАЛОПЕРИОДА
	if strings.Trim(BeginPeriod, " ") != "," {
		tt := t.PrepareBoundaryPeriod(BeginPeriod)
		if tt.active == 0 {
			return ""
		}
		//DataEndCalc := tt.data
		BorderEndCalc := tt.border
		//TimeEndCalc := tt.Time
		//ValueBorderCalc := tt.value

		strConditionData = KeyWord + `tconst_1.date >= '` + BorderEndCalc + `'`
		KeyWord = "and "
	}
	//}

	//{ подготовка 2-го параметра РЕКВИЗИТЫ
	NameTempTable := "slicelast_" + NameTableSprav

	var listReqv []string = make([]string, 0)

	ModeEditData := 0
	ModeEditDocum := 0

	if ConditionRequisites[len(ConditionRequisites)-1] == ',' {
		ConditionRequisites = ConditionRequisites[:len(ConditionRequisites)-1]
	}

	ConditionRequisites = strings.Replace(ConditionRequisites, "(", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, ")", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\n", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\t", " ", -1)
	if strings.Trim(ConditionRequisites, " \t\n") != "" {
		listReqv = strings.Split(ConditionRequisites, ",")
	}

	allReqv := spravRec.GetRekvCount()
	for cntR := 0; cntR < allReqv; cntR++ {
		//for _, nameReqv := range listReqv {
		metaRekv := spravRec.GetRekvByNum(cntR)
		//metaRekv := spravRec.GetRekvByName(nameReqv)
		nameReqv := metaRekv.SID
		if len(listReqv) > 0 {
			if Find(listReqv, nameReqv) == len(listReqv) {
				continue
			}
		}
		if metaRekv.Period == 0 {
			continue
		}
		reqvID := IntToString(metaRekv.ID)
		if metaRekv.ChangeDoc == 1 {
			ModeEditDocum = ModeEditDocum + 1
			if ModeEditDocum == 1 {
				strConditionColumnsDoc = strConditionColumnsDoc + reqvID
			} else {
				strConditionColumnsDoc = strConditionColumnsDoc + "," + reqvID
			}
		} else {
			ModeEditData = ModeEditData + 1
			if ModeEditData == 1 {
				strConditionColumnsData = strConditionColumnsData + reqvID
			} else {
				strConditionColumnsData = strConditionColumnsData + "," + reqvID
			}
		}
		txtValue := t.PrepareValue(metaRekv._MDRec, "slicelast")
		strConditionColumn = strConditionColumn + ",case when slicelast.id = " + reqvID +
			" then " + txtValue + " end " + nameReqv + "\n	"
		strGroupColumns = strGroupColumns + ",max(vt_slicelast." + nameReqv + ") as " + nameReqv + "\n	"
	}
	if ModeEditData > 1 {
		strConditionColumnsData = KeyWord + "tconst_1.id in (" + strConditionColumnsData + ")"
	} else {
		strConditionColumnsData = KeyWord + "tconst_1.id = " + strConditionColumnsData
	}
	if ModeEditDocum > 1 {
		strConditionColumnsDoc = KeyWord + "tconst_1.id in (" + strConditionColumnsDoc + ")"
	} else {
		strConditionColumnsDoc = KeyWord + "tconst_1.id = " + strConditionColumnsDoc
	}
	KeyWord = " and "
	//}

	//{ подготовка 3-го параметра ДОПОЛНИТЕЛЬНЫЕ УСЛОВИЯ
	if strings.Trim(AdditionalConditions, " ") != "," {
		strAddCondition = " and "
	}
	strAddCondition = strAddCondition + t.PrepareConditionBySliceFirstLast(AdditionalConditions, "tconst_1")
	//}

	//{ подготовка 4-го параметра СОЕДИНЕНИЕ
	strJoin = "\n" + t.PrepareConditionBySliceFirstLast(Join, "tconst_1")
	//}

	tmpStr := ""
	if ExpandPeriods == 1 {
		tmpStr = ",vt_slicelast.Дата,vt_slicelast.Время,vt_slicelast.Документ"
	}

	txtQuery = txtQuery + `SELECT
		vt_slicelast.ТекущийЭлемент
		` + tmpStr + `
		` + strGroupColumns + `
		from (
			select
				slicelast.objid ТекущийЭлемент
				`
	if ExpandPeriods == 1 {
		txtQuery = txtQuery + `,slicelast.date Дата,slicelast.time Время,slicelast.docid Документ
				`
	}
	txtQuery = txtQuery + `
		` + strConditionColumn + `
				from (`
	if ModeEditData > 0 {
		txtQuery = txtQuery + `
			select tconst_2.objid, tconst_2.id, tconst_2.date, 0 time, '     0   ' docid, tconst_2.value
			from (
				select tconst_1.objid, tconst_1.id, max(tconst_1.date) date
				from _1SCONST tconst_1 (NOLOCK)
				` + strJoin + `
				` + strConditionData + `
				` + strConditionColumnsData + `
				` + strAddCondition + `
				group by tconst_1.id,  tconst_1.objid) slicelast1
			inner join _1SCONST tconst_2 (NOLOCK)
			on slicelast1.id = tconst_2.id
			and slicelast1.objid = tconst_2.objid
			and slicelast1.date = tconst_2.date`
	}

	if ModeEditDocum > 0 {
		if ModeEditData > 0 {
			txtQuery = txtQuery + `
				UNION ALL
				`
		}
		txtQuery = txtQuery + `
						select tconst_4.objid, tconst_4.id, tconst_4.date, tconst_4.time, tconst_4.docid, tconst_4.value
						from (
							select tconst_3.objid, tconst_3.id, tconst_3.date, tconst_3.time, max(tconst_3.docid) docid
							from (
								select tconst_2.objid, tconst_2.id, tconst_2.date, max(tconst_2.time) time
								from (
									select tconst_1.objid, tconst_1.id, max(tconst_1.date) date
									from _1SCONST tconst_1 (NOLOCK)
									` + strJoin + `
									` + strConditionData + `
									` + strConditionColumnsDoc + `
									` + strAddCondition + `
									group by tconst_1.id, tconst_1.objid) slicelast1
								inner join _1SCONST tconst_2 (NOLOCK)
								on slicelast1.id = tconst_2.id
								and slicelast1.objid = tconst_2.objid
								and slicelast1.date = tconst_2.date
								group by tconst_2.id, tconst_2.objid, tconst_2.date) slicelast2				
							inner join _1SCONST tconst_3 (NOLOCK)
							on slicelast2.id = tconst_3.id
							and slicelast2.objid = tconst_3.objid
							and slicelast2.date = tconst_3.date
							and slicelast2.time = tconst_3.time
							group by tconst_3.id, tconst_3.objid, tconst_3.date, tconst_3.time) slicelast3
						inner join _1SCONST tconst_4 (NOLOCK)
						on slicelast3.id = tconst_4.id
						and slicelast3.objid = tconst_4.objid
						and slicelast3.date = tconst_4.date
						and slicelast3.time = tconst_4.time
						and slicelast3.docid = tconst_4.docid
			`
	}
	txtQuery = txtQuery + `		) slicelast
		) vt_slicelast
		group by vt_slicelast.ТекущийЭлемент
		`
	if ExpandPeriods == 1 {
		txtQuery = txtQuery + `		,vt_slicelast.Дата,vt_slicelast.Время,vt_slicelast.Документ`
	}
	txtQuery = strings.Replace(txtQuery, "slicelast", NameTempTable, -1)

	txtQuery = "( " + txtQuery + " ) "

	return txtQuery
}

// История_DBF_SQL
func (t *MetaDataWork) History_DBF_SQL(res []string) string {
	txtQuery := ""

	//var ExpandPeriods int
	//var err error

	SpravID := res[1]
	BeginPeriod := res[2]
	EndPeriod := res[3]
	ConditionRequisites := res[4]
	AdditionalConditions := res[5]
	Join := res[6]

	spravRec := t.GetSpravByName(SpravID)
	strColumn := ""
	strConditionBeginPeriod := ""
	strConditionEndPeriod := ""
	strAddCondition := ""
	StrConditionRequisites := ""
	strJoin := ""
	KeyWord := "\nwhere "
	//NameTableSprav := "SC" + IntToString(spravRec.ID)

	//{ подготовка 1-го параметра НАЧАЛОПЕРИОДА
	if strings.Trim(BeginPeriod, " ") != "," {
		tt := t.PrepareBoundaryPeriod(BeginPeriod)
		if tt.active == 0 {
			return ""
		}
		//DataEndCalc := tt.data
		BorderEndCalc := tt.border
		//TimeEndCalc := tt.Time
		//ValueBorderCalc := tt.value

		strConditionBeginPeriod = KeyWord + `tconst_1.date >= '` + BorderEndCalc + `'`
		KeyWord = "and "
	}
	//}
	//{ подготовка 2-го параметра КОНЕЦПЕРИОДА
	if strings.Trim(EndPeriod, " ") != "," {
		tt := t.PrepareBoundaryPeriod(EndPeriod)
		if tt.active == 0 {
			return ""
		}
		//DataEndCalc := tt.data
		BorderEndCalc := tt.border
		//TimeEndCalc := tt.Time
		//ValueBorderCalc := tt.value

		strConditionEndPeriod = KeyWord + `tconst_1.date <= '` + BorderEndCalc + `'`
		KeyWord = "and "
	}
	//}

	//{ подготовка 3-го параметра РЕКВИЗИТЫ
	var listReqv []string = make([]string, 0)

	if ConditionRequisites[len(ConditionRequisites)-1] == ',' {
		ConditionRequisites = ConditionRequisites[:len(ConditionRequisites)-1]
	}

	ConditionRequisites = strings.Replace(ConditionRequisites, "(", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, ")", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\n", "", -1)
	ConditionRequisites = strings.Replace(ConditionRequisites, "\t", " ", -1)
	if strings.Trim(ConditionRequisites, " \t\n") != "" {
		listReqv = strings.Split(ConditionRequisites, ",")
	}

	strValueRequisites := ""

	allReqv := spravRec.GetRekvCount()
	for cntR := 0; cntR < allReqv; cntR++ {
		metaRekv := spravRec.GetRekvByNum(cntR)
		//metaRekv := spravRec.GetRekvByName(nameReqv)
		nameReqv := metaRekv.SID
		if len(listReqv) > 0 {
			if Find(listReqv, nameReqv) == len(listReqv) {
				continue
			}
		}
		if metaRekv.Period == 0 {
			continue
		}
		reqvID := IntToString(metaRekv.ID)
		txtValue := t.PrepareValue(metaRekv._MDRec, "history")
		if strings.Trim(strValueRequisites, " \t\n") != "" {
			strValueRequisites = strValueRequisites + " , " + reqvID
		} else {
			strValueRequisites = reqvID
		}
		strColumn = strColumn + ",case when history.id = " + reqvID + " then " + txtValue + " end " + nameReqv + "\r\n"
	}
	StrConditionRequisites = KeyWord + " history.id "
	if len(listReqv) > 1 {
		StrConditionRequisites = StrConditionRequisites + " in ("
	} else {
		StrConditionRequisites = StrConditionRequisites + "= "
	}
	StrConditionRequisites = StrConditionRequisites + strValueRequisites
	if len(listReqv) > 1 {
		StrConditionRequisites = StrConditionRequisites + ")"
	}
	KeyWord = " and "
	//}

	//{ подготовка 4-го параметра ДОПОЛНИТЕЛЬНЫЕ УСЛОВИЯ
	if strings.Trim(AdditionalConditions, " ") != "," {
		strAddCondition = " and "
	}
	strAddCondition = strAddCondition + t.PrepareConditionBySliceFirstLast(AdditionalConditions, "tconst_1")
	//}

	//{ подготовка 5-го параметра СОЕДИНЕНИЕ
	strJoin = "\n" + t.PrepareConditionBySliceFirstLast(Join, "tconst_1")
	//}

	txtQuery = txtQuery + `	select
			history.objid ТекущийЭлемент
			,history.date Дата
			,history.time Время
			,history.docid Документ
			` + strColumn + `
		FROM _1SCONST history (NOLOCK)
		` + strJoin + `
		` + strConditionBeginPeriod + `
		` + strConditionEndPeriod + `
		` + StrConditionRequisites + `
		` + strAddCondition

	txtQuery = "( " + txtQuery + " ) "

	return txtQuery
}

// ПарсингВТСрезПоследних
func (t *MetaDataWork) ParsingVTSliceLatest(v string) string {
	Param := t.GetStringParam(5)
	Pattern := `\$СрезПоследних\.([\wа-яё]+[^\wа-яё\(]*)\(` + Param
	re := t.GetParametersExpressions(Pattern, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {
		strChange := t.SliceLast_DBF_SQL(res[i])
		if strChange != "" {
			v = strings.Replace(v, res[i][0], strChange, -1)
		}
	}

	return v

}

// ПарсингВТСрезПервых
func (t *MetaDataWork) ParsingVTScutFirst(v string) string {
	Param := t.GetStringParam(5)
	Pattern := `\$СрезПервых\.([\wа-яё]+[^\wа-яё\(]*)\(` + Param
	re := t.GetParametersExpressions(Pattern, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {
		strChange := t.SliceFirst_DBF_SQL(res[i])
		if strChange != "" {
			v = strings.Replace(v, res[i][0], strChange, -1)
		}
	}

	return v

}

// ПарсингВТИстория
func (t *MetaDataWork) ParsingVTIhistory(v string) string {
	Param := t.GetStringParam(5)
	Pattern := `\$История\.([\wа-яё]+[^\wа-яё\(]*)\(` + Param
	re := t.GetParametersExpressions(Pattern, v)
	if re == nil {
		return v
	}
	res := re.FindAllStringSubmatch(v, -1)
	for i := range res {
		strChange := t.History_DBF_SQL(res[i])
		if strChange != "" {
			v = strings.Replace(v, res[i][0], strChange, -1)
		}
	}

	return v

}

func (t *MetaDataWork) ParseQuery(v string) (string, error) {

	var db *sql.DB
	var err error

	if t.ConnectInfo.Server != "" {

		strConnection := t.GetConnectString()
		db, err = sql.Open("sqlserver", strConnection)
		if err != nil {
			fmt.Printf("Error SliceLast_DBF_SQL %s", err.Error())
			return "", err
		}

		CreateFunctionStrToId(db)
		CreateFunctionIntToTime(db)

		db.Close()

		t.CalculateBoundariesTA()
		v = t.ParseLastValue(v)
		t.FillTableOfSources(v)
		v = t.ParsingDataSources(v)

		v = t.ParsingTableAttributes(v)
		//ПарсингВТРегистрОстатки
		v = t.ParsingVTRegisterBalances(v)

		//ПарсингВТСрезПоследних
		v = t.ParsingVTSliceLatest(v)
		//ПарсингВТСрезПервых
		v = t.ParsingVTScutFirst(v)
		//ПарсингВТИстория
		v = t.ParsingVTIhistory(v)
	}
	v = t.ParseParameters(v)
	for i := range t.SubQuery {
		v = t.SubQuery[i] + "\n" + v
	}

	return v, nil
}

func (t MetaDataWork) TableNameRegItog(v string) string {
	r := t.GetRegistrByName(v)
	if r.ID == 0 {
		return v
	}

	return fmt.Sprintf("rg%d", r.ID)
}

func (t MetaDataWork) TableNameRegMove(v string) string {
	r := t.GetRegistrByName(v)
	if r.ID == 0 {
		return v
	}

	return fmt.Sprintf("ra%d", r.ID)
}

func (t MetaDataWork) ReferenceTableName(v string) string {
	r := t.GetSpravByName(v)
	if r.ID == 0 {
		return v
	}

	return fmt.Sprintf("sc%d", r.ID)
}

func (t MetaDataWork) DocHeadTableName(v string) string {
	r := t.GetDocByName(v)
	if r.ID == 0 {
		return v
	}

	return fmt.Sprintf("dh%d", r.ID)
}

func (t MetaDataWork) DocTableName(v string) string {
	r := t.GetDocByName(v)
	if r.ID == 0 {
		return v
	}

	return fmt.Sprintf("dt%d", r.ID)
}

func (t MetaDataWork) ParseLastValue(src string) string {
	Param := t.GetStringParam(2)
	Pattern := `\$ПоследнееЗначение\.([\wа-яА-Яё]+)\.([\wа-яА-Яё]+[^\wа-яё\(]*)\(` + Param
	matched, err := regexp.Match(Pattern, []byte(src))
	if err != nil {
		fmt.Println(err.Error())
		os.Exit(1)
	}
	if !matched {
		return src
	}
	re := regexp.MustCompile(Pattern)
	retStr := src
	res := re.FindAllStringSubmatch(src, -1)
	for i := range res {
		//fmt.Printf("%s\n", res[i])
		strNone := res[i][0]
		ObjectProps := res[i][1]                 //ОбъектРеквизита
		PropsID := res[i][2]                     //ИдентификаторРеквизита
		Element := t.PrepareParameter(res[i][3]) //Элемент
		BoundaryValues := ""
		if len(res[i]) >= 4 {
			BoundaryValues = t.PrepareParameter(res[i][4])
		} //ГраницаЗначения
		//fmt.Printf("ObjectProps=%s PropsID=%s Element=%s BoundaryValues=%s\n", ObjectProps, PropsID, Element, BoundaryValues)

		metaProps := t.GetConstantaMetaProp(PropsID)
		if metaProps.ID == 0 {
			metaProps = t.GetSpravMetaProp(ObjectProps, PropsID)
		}
		//fmt.Printf("%q\n", metaProps)
		valHistory := IntToString(metaProps.ID)
		ColumnID := t.PrepareValue(metaProps, "const_vt")
		//fmt.Printf("ColumnID=%s valHistory=%s\n", ColumnID, valHistory)

		BoundaryValuesThisParameter := 1                                              //ГраницаЗначенияЭтоПараметр
		DateEndCalculations := time.Now()                                             //ДатаОкончРасчетов
		BorderEndCalculations := `'` + t.GetStringFromDate(DateEndCalculations) + `'` //ГраницаОкончРасчетов
		//TimeEndCalculations := "     0"                                               //ВремяОкончРасчетов
		//IDDEndCalculations := "     0   "                                             //ИДДокОкончРасчетов
		//ConditionByDocumentPosition := 0                                              //УсловиеПоПозицииДокумента
		//Modifier := 0                                                                 //Модификатор
		if BoundaryValues == "" {
			BoundaryValuesThisParameter = -1
		} else {
			if BoundaryValues[0] == ':' {
				vector := t.PrepareBoundaryPeriod(BoundaryValues)
				if vector.active == 0 {
					return ""
				}
				DateEndCalculations = vector.data
				BorderEndCalculations = vector.border
				if BorderEndCalculations[0] != '\'' {
					BorderEndCalculations = "'" + BorderEndCalculations + "'"
				}
				//TimeEndCalculations = vector.Time[:6]
				//IDDEndCalculations = vector.Time[6:15]
			} else {
				BoundaryValuesThisParameter = 0
				BorderEndCalculations = strings.Trim(BoundaryValues, " ")
				//IDDEndCalculations = "''"
			}
		}
		if (metaProps.ChangeDoc == 1) && (BoundaryValuesThisParameter == -1) {
			DateEndCalculations = DateEndCalculations.Add(24 * time.Hour) // добавить 1 день к дате
			// Добавить годы, месеца и дни к дате
			//DateEndCalculations = DateEndCalculations.AddDate(Year, Month, Day)
			BorderEndCalculations = `'` + t.GetStringFromDate(DateEndCalculations) + `'`
		}
		//fmt.Printf("BoundaryValuesThisParameter=%d BorderEndCalculations=%s TimeEndCalculations=%s IDDEndCalculations=%s ConditionByDocumentPosition=%d Modifier=%d\n",
		//	BoundaryValuesThisParameter, BorderEndCalculations, TimeEndCalculations, IDDEndCalculations, ConditionByDocumentPosition, Modifier)

		strCompare := "const_vt.DATE < " + BorderEndCalculations
		TextSubstitutions := "(SELECT TOP 1 " + ColumnID + "\n" +
			"FROM _1SCONST const_vt (NOLOCK)\n" +
			"WHERE const_vt.ID = " + valHistory + "\n" +
			"AND const_vt.OBJID = " + Element + "\n" +
			"AND " + strCompare + "\n" +
			"ORDER BY const_vt.DATE DESC,const_vt.TIME DESC,const_vt.DOCID DESC,const_vt.ROW_ID DESC)"

		retStr = strings.Replace(retStr, strNone, TextSubstitutions, -1)
	}
	return retStr
}

func NewMetaDataWork() MetaDataWork {

	t := new(MetaDataWork)
	t.fileMetadata = ""
	t.strMetaData = ""

	t.templParam = `(?:\((?:[^()]|"[^"]*"|'[^']*'|\((?:[^()]|"[^"]*"|'[^']*'|\((?:[^()]|"[^"]*"|'[^']*'|\([^()]*\))*\))*\))*\)|"[^"]*"|'[^']*'|[^,()"'])*`

	t.c = *new(CMMS)

	//var v MDRecCol

	//v = NewMDRecCol()
	t.commonProp = NewMDRecCol()
	t.sprav = NewMDRecCol()
	t.consts = NewMDRecCol() //&v
	t.enumList = NewMDRecCol()
	t.docList = NewMDRecCol()
	t.regList = NewMDRecCol()

	t.Param = make(map[string]interface{})
	t.ObjectsByID = make(map[string]MDObject)
	t.ObjectsByDescr = make(map[string]MDObject)

	t.TableOfType = make(map[string]TableType)

	return *t
}

// exists returns whether the given file or directory exists or not
func exists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return true, err
}

func GetFileStat(fileName string) (os.FileInfo, error) {

	stat, err := os.Stat(fileName)

	return stat, err
}

func (t MetaDataWork) GetConnectString() string {

	return fmt.Sprintf("server=%s;user id=%s;password=%s;port=%d;database=%s;encrypt=disable",
		t.ConnectInfo.Server, t.ConnectInfo.User, t.ConnectInfo.Psw, 1433, t.ConnectInfo.DB)

}

func (t *MetaDataWork) AttachFromSQL(db *sql.DB, FirmaID int) error {
	var rows *sql.Rows
	var err error

	ctx := context.Background()
	err = db.PingContext(ctx)
	if err != nil {
		return err
	}

	Query := fmt.Sprintf("SELECT [Value] FROM Analiz_EN.dbo.MdFile WHERE FirmaID=%d AND [FileName]='1Cv7.DBA'", FirmaID)
	rows, err = db.QueryContext(ctx, Query)
	if err != nil {
		return err
	}
	var tmpConn string
	for rows.Next() {

		err = rows.Scan(&tmpConn)
		if err != nil {
			return err
		}
	}

	t.ConnectInfo = *new(ParseDBA.ConnectInfo)
	t.ConnectInfo.ParseConnect(tmpConn)

	Query = fmt.Sprintf("SELECT [Value] FROM Analiz_EN.dbo.MdFile WHERE FirmaID=%d AND [FileName]='1Cv7.MD'", FirmaID)
	rows, err = db.QueryContext(ctx, Query)
	if err != nil {
		return err
	}
	for rows.Next() {

		err = rows.Scan(&tmpConn)
		if err != nil {
			return err
		}
	}

	var c CMMS = GetCMMS_FromString(tmpConn)
	// var data []byte

	// data, err = ioutil.ReadFile(FileMDP)
	// err = json.Unmarshal(data, &c)
	t.c = c

	//GetCMMS_FromString(filename string)

	t.ParseMD()

	return nil

}

func (t *MetaDataWork) AttachMD(fileName string) {

	var data []byte

	t.fileMetadata = strings.Trim(fileName, " ")
	FileMDP := t.fileMetadata + ".cache"
	extension := filepath.Ext(fileName)
	FileDBA := strings.Replace(fileName, extension, ".DBA", -1)

	bExist, err := exists(t.fileMetadata)
	if !bExist {
		return
	}
	bExist, err = exists(FileDBA)
	if !bExist {
		return
	}

	t.ConnectInfo = *new(ParseDBA.ConnectInfo)
	t.ConnectInfo.ParseDBA(FileDBA)

	//	fmt.Printf("FileMDP=%s extension=%s FileDBA=%s err=%s", FileMDP, extension, FileDBA, err)

	bExist, err = exists(FileMDP)
	if !bExist {

		//statFileMD, _ := GetFileStat(t.fileMetadata)
		//fmt.Print("\n")
		//fmt.Print(statFileMD)

		t.c = GetCMMS(fileName)

		data, err = json.Marshal(t.c)
		File, _Err := os.Create(FileMDP)
		if _Err != nil {
			fmt.Println("Unable to create file:", err)
			os.Exit(1)
		}
		File.Write(data)
		File.Close()
	} else {

		statFileMD, _ := GetFileStat(t.fileMetadata)
		statFileMDP, _ := GetFileStat(FileMDP)
		statFileDBA, _ := GetFileStat(FileDBA)

		tmFileMD := statFileMD.ModTime()
		tmFileMDP := statFileMDP.ModTime()
		tmFileDBA := statFileDBA.ModTime()

		if tmFileMDP.Before(tmFileMD) || tmFileMDP.Before(tmFileDBA) {
			t.c = GetCMMS(fileName)

			data, err = json.Marshal(t.c)
			File, _Err := os.Create(FileMDP)
			if _Err != nil {
				fmt.Println("Unable to create file:", err)
				os.Exit(1)
			}
			File.Write(data)
			File.Close()
		} else {
			var c CMMS = *new(CMMS)
			data, err = ioutil.ReadFile(FileMDP)
			err = json.Unmarshal(data, &c)
			t.c = c
		}
	}

	t.ParseMD()
}

func (t *MetaDataWork) ParseMD() error {

	for i := 0; i < len(t.c.Children); i++ {
		obj := t.c.Children[i]
		if obj.SID == "GenJrnlFldDef" {
			//vv := NewMDRecCol()
			t.commonProp = NewMDRecCol() //&vv
			t.commonProp.StrMeta = "ОбщиеПоля"
			t.commonProp.TypeMd = md_FldDef
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				objFld := NewCommonProp_01(tmp.Params)
				t.commonProp.Add(objFld.SID, fmt.Sprintf("%d", objFld.ID), objFld)

				d := NewMDObject(objFld, "Общийреквизит."+objFld.SID)

				t.ObjectsByID[IntToString(objFld.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d //strings.ToUpper(sid)
			}
		} else if obj.SID == "SbCnts" {
			//vv := NewMDRecCol()
			t.sprav = NewMDRecCol() //&vv
			t.sprav.StrMeta = "Справочник"
			t.sprav.TypeMd = md_Sprav
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				objSprav := NewSpravRec_01(tmp.Params)
				tmp = tmp.Children[0] // Пропускаем Params
				/*				if objSprav.SID == "Номенклатура" {

									//data, err := json.Marshal(tmp)
									File, _Err := os.Create("D:\\Номенклатура.prm")
									if _Err != nil {
										fmt.Println("Unable to create file:", _Err)
										os.Exit(1)
									}
									//File.Write(data)
									for k := 0; k < len(tmp.Children); k++ {
										tmp1 := tmp.Children[k]
										fmt.Fprintf(File, "%q\n", tmp1)
									}
									File.Close()

								}
				*/
				for k := 0; k < len(tmp.Children); k++ {
					tmp1 := tmp.Children[k]
					objSpravParam := NewSpravParam_01(tmp1.Params)
					objSprav.Add(objSpravParam.SID, fmt.Sprintf("%d", objSpravParam.ID), objSpravParam)

					d := NewMDObject(objSpravParam, "Справочник."+objSprav.SID+"."+objSpravParam.SID)
					t.ObjectsByID[IntToString(objSpravParam.ID)] = d
					t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
				}
				t.sprav.Add(objSprav.SID, fmt.Sprintf("%d", objSprav.ID), objSprav)

				d := NewMDObject(objSprav, "Справочник."+objSprav.SID)

				t.ObjectsByID[IntToString(objSprav.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
			}
		} else if obj.SID == "Consts" {
			//vv := NewMDRecCol()
			t.consts = NewMDRecCol() //&vv
			t.consts.StrMeta = "Константа"
			t.consts.TypeMd = md_Const
			/*
				File, _Err := os.Create("D:\\Константы.prm")
				if _Err != nil {
					fmt.Println("Unable to create file:", _Err)
					os.Exit(1)
				}
				//File.Write(data)
				for k := 0; k < len(obj.Children); k++ {
					tmp1 := obj.Children[k]
					fmt.Fprintf(File, "%q\n", tmp1)
				}
				File.Close()
			*/
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				objConst := NewConstRec_01(tmp.Params)

				d := NewMDObject(objConst, "Константа."+objConst.SID)

				t.ObjectsByID[IntToString(objConst.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d //strings.ToUpper(sid)

				t.consts.Add(objConst.SID, IntToString(objConst.ID), objConst)
			}
		} else if obj.SID == "EnumList" {
			//vv := NewMDRecCol()
			t.enumList = NewMDRecCol() //&vv
			t.enumList.StrMeta = "Перечисление"
			t.enumList.TypeMd = md_Enum
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				en := NewEnumRec_01(tmp.Params)
				//en := &_en
				tmp = tmp.Children[0] // Пропускаем Params
				for k := 0; k < len(tmp.Children); k++ {
					tmp1 := tmp.Children[k]
					objEnumVal := NewEnumVal_01(tmp1.Params)
					en = en.Add(objEnumVal.SID, fmt.Sprintf("%d", objEnumVal.ID), objEnumVal)

					d := NewMDObject(objEnumVal, "Перечисление."+en.SID+"."+objEnumVal.SID)
					t.ObjectsByID[IntToString(objEnumVal.ID)] = d
					t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
				}

				d := NewMDObject(en, "Перечисление."+en.SID)

				t.ObjectsByID[IntToString(en.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d

				t.enumList = t.enumList.Add(en.SID, IntToString(en.ID), en)
			}
		} else if obj.SID == "Documents" {
			//vv := NewMDRecCol()
			t.docList = NewMDRecCol() //&vv
			t.docList.StrMeta = "Документ"
			t.docList.TypeMd = md_Doc
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				objDoc := NewDocRec_01(tmp.Params)
				/*
					if j == 0 {

						File, _Err := os.Create("D:\\Документ" + objDoc.Desc + ".prm")
						if _Err != nil {
							fmt.Println("Unable to create file:", _Err)
							os.Exit(1)
						}
						for l := 0; l < len(tmp.Children); l++ {
							tmpDoc := tmp.Children[l]
							if tmpDoc.SID == "Head Fields" {
								File.WriteString("======== Head Fields ========\n")
								for k := 0; k < len(tmpDoc.Children); k++ {
									tmpDC := tmpDoc.Children[k]
									fmt.Fprintf(File, "%q\n", tmpDC)
								}
							} else if tmpDoc.SID == "Table Fields" {
								File.WriteString("======== Table Fields ========\n")
								for k := 0; k < len(tmpDoc.Children); k++ {
									tmpDC := tmpDoc.Children[k]
									fmt.Fprintf(File, "%q\n", tmpDC)
								}
							}
						}
						File.Close()
					}
				*/
				for l := 0; l < len(tmp.Children); l++ {
					tmpDoc := tmp.Children[l]
					if tmpDoc.SID == "Head Fields" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objDocHead := NewDocHead_01(tmpDC.Params)
							objDoc.AddHead(objDocHead.SID, IntToString(objDocHead.ID), objDocHead)

							d := NewMDObject(objDocHead, "Документ."+objDoc.SID+"."+objDocHead.SID)
							t.ObjectsByID[IntToString(objDocHead.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
						}
					} else if tmpDoc.SID == "Table Fields" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objDocTable := NewDocTable_01(tmpDC.Params)
							objDoc.AddTable(objDocTable.SID, IntToString(objDocTable.ID), objDocTable)

							d := NewMDObject(objDocTable, "Документ."+objDoc.SID+"."+objDocTable.SID)
							t.ObjectsByID[IntToString(objDocTable.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d

							if objDocTable.Itog == 1 {
								objDocHead := NewDocHead_01(tmpDC.Params)
								objDoc.AddHead(objDocHead.SID, IntToString(objDocHead.ID), objDocHead)

								d := NewMDObject(objDocHead, "Документ."+objDoc.SID+"."+objDocHead.SID)
								t.ObjectsByID[IntToString(objDocHead.ID)] = d
								t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
							}
						}
					}
				}
				t.docList.Add(objDoc.SID, IntToString(objDoc.ID), objDoc)

				d := NewMDObject(objDoc, "Документ."+objDoc.SID)

				t.ObjectsByID[IntToString(objDoc.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
			}
		} else if obj.SID == "Registers" {
			//vv := NewMDRecCol()
			t.regList = NewMDRecCol() //&vv
			t.regList.StrMeta = "Регистр"
			t.regList.TypeMd = md_Register
			for j := 0; j < len(obj.Children); j++ {
				tmp := obj.Children[j]
				objReg := NewRegRec_01(tmp.Params)
				for l := 0; l < len(tmp.Children); l++ {
					tmpDoc := tmp.Children[l]
					if tmpDoc.SID == "Props" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objRegIzm := NewRegIzm_01(tmpDC.Params)
							objReg.AddIzm(objRegIzm.SID, IntToString(objRegIzm.ID), objRegIzm)

							d := NewMDObject(objRegIzm, "Регистр."+objReg.SID+"."+objRegIzm.SID)
							t.ObjectsByID[IntToString(objRegIzm.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
						}
					} else if tmpDoc.SID == "Figures" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objRegRes := NewRegRes_01(tmpDC.Params)
							objReg.AddResurs(objRegRes.SID, IntToString(objRegRes.ID), objRegRes)

							d := NewMDObject(objRegRes, "Регистр."+objReg.SID+"."+objRegRes.SID)
							t.ObjectsByID[IntToString(objRegRes.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
						}
					} else if tmpDoc.SID == "Figures" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objRegRes := NewRegRes_01(tmpDC.Params)
							objReg.AddResurs(objRegRes.SID, IntToString(objRegRes.ID), objRegRes)

							d := NewMDObject(objRegRes, "Регистр."+objReg.SID+"."+objRegRes.SID)
							t.ObjectsByID[IntToString(objRegRes.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
						}
					} else if tmpDoc.SID == "Flds" {
						for k := 0; k < len(tmpDoc.Children); k++ {
							tmpDC := tmpDoc.Children[k]
							objRegReq := NewRegReq_01(tmpDC.Params)
							objReg.AddRekv(objRegReq.SID, IntToString(objRegReq.ID), objRegReq)

							d := NewMDObject(objRegReq, "Регистр."+objReg.SID+"."+objRegReq.SID)
							t.ObjectsByID[IntToString(objRegReq.ID)] = d
							t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
						}
					}
				}
				t.regList.Add(objReg.SID, IntToString(objReg.ID), objReg)

				d := NewMDObject(objReg, "Регистр."+objReg.SID)

				t.ObjectsByID[IntToString(objReg.ID)] = d
				t.ObjectsByDescr[strings.ToUpper(d.objDescr)] = d
			}
		}
	}

	return nil
}

//=======================  КОНЕЦ MetaDataWork  ===========================================

// A field represents a single field found in a struct.
type field struct {
	name      string
	nameBytes []byte                 // []byte(name)
	equalFold func(s, t []byte) bool // bytes.EqualFold or equivalent

	nameNonEsc  string // `"` + name + `":`
	nameEscHTML string // `"` + HTMLEscape(name) + `":`

	tag       bool
	index     []int
	typ       reflect.Type
	omitEmpty bool
	quoted    bool

	//	encoder encoderFunc
}

type structFields struct {
	list      []field
	nameIndex map[string]int
}

const (
	caseMask     = ^byte(0x20) // Mask to ignore case in ASCII.
	kelvin       = '\u212a'
	smallLongEss = '\u017f'
)

func getTypeName(ptr interface{}) string {
	ptrType := reflect.TypeOf(ptr)
	arrayType := ptrType.Elem()
	elementType := arrayType.Elem()
	typeName := elementType.Name()
	return typeName

	// objType := reflect.TypeOf(obj)

	// typeName := ""
	// v := reflect.ValueOf(obj)
	// if v.Kind() == reflect.Ptr {
	// 	//objType := reflect.TypeOf(obj)
	// 	elemType := objType.Elem()
	// 	typeName = elemType.Name()
	// } else {
	// 	typeName = objType.Name()
	// }
	// return typeName
}

// foldFunc returns one of four different case folding equivalence
// functions, from most general (and slow) to fastest:
//
// 1) bytes.EqualFold, if the key s contains any non-ASCII UTF-8
// 2) equalFoldRight, if s contains special folding ASCII ('k', 'K', 's', 'S')
// 3) asciiEqualFold, no special, but includes non-letters (including _)
// 4) simpleLetterEqualFold, no specials, no non-letters.
//
// The letters S and K are special because they map to 3 runes, not just 2:
//   - S maps to s and to U+017F 'Еї' Latin small letter long s
//   - k maps to K and to U+212A 'в„Є' Kelvin sign
//
// See https://play.golang.org/p/tTxjOc0OGo
//
// The returned function is specialized for matching against s and
// should only be given s. It's not curried for performance reasons.
func foldFunc(s []byte) func(s, t []byte) bool {
	nonLetter := false
	special := false // special letter
	for _, b := range s {
		if b >= utf8.RuneSelf {
			return bytes.EqualFold
		}
		upper := b & caseMask
		if upper < 'A' || upper > 'Z' {
			nonLetter = true
		} else if upper == 'K' || upper == 'S' {
			// See above for why these letters are special.
			special = true
		}
	}
	if special {
		return equalFoldRight
	}
	if nonLetter {
		return asciiEqualFold
	}
	return simpleLetterEqualFold
}

// equalFoldRight is a specialization of bytes.EqualFold when s is
// known to be all ASCII (including punctuation), but contains an 's',
// 'S', 'k', or 'K', requiring a Unicode fold on the bytes in t.
// See comments on foldFunc.
func equalFoldRight(s, t []byte) bool {
	for _, sb := range s {
		if len(t) == 0 {
			return false
		}
		tb := t[0]
		if tb < utf8.RuneSelf {
			if sb != tb {
				sbUpper := sb & caseMask
				if 'A' <= sbUpper && sbUpper <= 'Z' {
					if sbUpper != tb&caseMask {
						return false
					}
				} else {
					return false
				}
			}
			t = t[1:]
			continue
		}
		// sb is ASCII and t is not. t must be either kelvin
		// sign or long s; sb must be s, S, k, or K.
		tr, size := utf8.DecodeRune(t)
		switch sb {
		case 's', 'S':
			if tr != smallLongEss {
				return false
			}
		case 'k', 'K':
			if tr != kelvin {
				return false
			}
		default:
			return false
		}
		t = t[size:]

	}
	if len(t) > 0 {
		return false
	}
	return true
}

// asciiEqualFold is a specialization of bytes.EqualFold for use when
// s is all ASCII (but may contain non-letters) and contains no
// special-folding letters.
// See comments on foldFunc.
func asciiEqualFold(s, t []byte) bool {
	if len(s) != len(t) {
		return false
	}
	for i, sb := range s {
		tb := t[i]
		if sb == tb {
			continue
		}
		if ('a' <= sb && sb <= 'z') || ('A' <= sb && sb <= 'Z') {
			if sb&caseMask != tb&caseMask {
				return false
			}
		} else {
			return false
		}
	}
	return true
}

// simpleLetterEqualFold is a specialization of bytes.EqualFold for
// use when s is all ASCII letters (no underscores, etc) and also
// doesn't contain 'k', 'K', 's', or 'S'.
// See comments on foldFunc.
func simpleLetterEqualFold(s, t []byte) bool {
	if len(s) != len(t) {
		return false
	}
	for i, b := range s {
		if b&caseMask != t[i]&caseMask {
			return false
		}
	}
	return true
}

// tagOptions is the string following a comma in a struct field's "json"
// tag, or the empty string. It does not include the leading comma.
type tagOptions string

// parseTag splits a struct field's json tag into its name and
// comma-separated options.
func parseTag(tag string) (string, tagOptions) {
	tag, opt, _ := strings.Cut(tag, ",")
	return tag, tagOptions(opt)
}

// Contains reports whether a comma-separated list of options
// contains a particular substr flag. substr must be surrounded by a
// string boundary or commas.
func (o tagOptions) Contains(optionName string) bool {
	if len(o) == 0 {
		return false
	}
	s := string(o)
	for s != "" {
		var name string
		name, s, _ = strings.Cut(s, ",")
		if name == optionName {
			return true
		}
	}
	return false
}

func isValidTag(s string) bool {
	if s == "" {
		return false
	}
	for _, c := range s {
		switch {
		case strings.ContainsRune("!#$%&()*+-./:;<=>?@[]^_{|}~ ", c):
			// Backslash and quote chars are reserved, but
			// otherwise any punctuation chars are allowed
			// in a tag name.
		case !unicode.IsLetter(c) && !unicode.IsDigit(c):
			return false
		}
	}
	return true
}

var hex = "0123456789abcdef"

// HTMLEscape appends to dst the JSON-encoded src with <, >, &, U+2028 and U+2029
// characters inside string literals changed to \u003c, \u003e, \u0026, \u2028, \u2029
// so that the JSON will be safe to embed inside HTML <script> tags.
// For historical reasons, web browsers don't honor standard HTML
// escaping within <script> tags, so an alternative JSON encoding must
// be used.
func HTMLEscape(dst *bytes.Buffer, src []byte) {
	// The characters can only appear in string literals,
	// so just scan the string one byte at a time.
	start := 0
	for i, c := range src {
		if c == '<' || c == '>' || c == '&' {
			if start < i {
				dst.Write(src[start:i])
			}
			dst.WriteString(`\u00`)
			dst.WriteByte(hex[c>>4])
			dst.WriteByte(hex[c&0xF])
			start = i + 1
		}
		// Convert U+2028 and U+2029 (E2 80 A8 and E2 80 A9).
		if c == 0xE2 && i+2 < len(src) && src[i+1] == 0x80 && src[i+2]&^1 == 0xA8 {
			if start < i {
				dst.Write(src[start:i])
			}
			dst.WriteString(`\u202`)
			dst.WriteByte(hex[src[i+2]&0xF])
			start = i + 3
		}
	}
	if start < len(src) {
		dst.Write(src[start:])
	}
}

// byIndex sorts field by index sequence.
type byIndex []field

func (x byIndex) Len() int { return len(x) }

func (x byIndex) Swap(i, j int) { x[i], x[j] = x[j], x[i] }

func (x byIndex) Less(i, j int) bool {
	for k, xik := range x[i].index {
		if k >= len(x[j].index) {
			return false
		}
		if xik != x[j].index[k] {
			return xik < x[j].index[k]
		}
	}
	return len(x[i].index) < len(x[j].index)
}

// typeFields returns a list of fields that JSON should recognize for the given type.
// The algorithm is breadth-first search over the set of structs to include - the top struct
// and then any reachable anonymous structs.
func typeFields(t reflect.Type) structFields {
	// Anonymous fields to explore at the current level and the next.
	current := []field{}
	next := []field{{typ: t}}

	// Count of queued names for current level and the next.
	var count, nextCount map[reflect.Type]int

	// Types already visited at an earlier level.
	visited := map[reflect.Type]bool{}

	// Fields found.
	var fields []field

	// Buffer to run HTMLEscape on field names.
	var nameEscBuf bytes.Buffer

	for len(next) > 0 {
		current, next = next, current[:0]
		count, nextCount = nextCount, map[reflect.Type]int{}

		for _, f := range current {
			if visited[f.typ] {
				continue
			}
			visited[f.typ] = true

			// Scan f.typ for fields to include.
			for i := 0; i < f.typ.NumField(); i++ {
				sf := f.typ.Field(i)
				if sf.Anonymous {
					t := sf.Type
					if t.Kind() == reflect.Pointer {
						t = t.Elem()
					}
					if !sf.IsExported() && t.Kind() != reflect.Struct {
						// Ignore embedded fields of unexported non-struct types.
						continue
					}
					// Do not ignore embedded fields of unexported struct types
					// since they may have exported fields.
				} else if !sf.IsExported() {
					// Ignore unexported non-embedded fields.
					continue
				}
				tag := sf.Tag.Get("json")
				if tag == "-" {
					continue
				}
				name, opts := parseTag(tag)
				if !isValidTag(name) {
					name = ""
				}
				index := make([]int, len(f.index)+1)
				copy(index, f.index)
				index[len(f.index)] = i

				ft := sf.Type
				if ft.Name() == "" && ft.Kind() == reflect.Pointer {
					// Follow pointer.
					ft = ft.Elem()
				}

				// Only strings, floats, integers, and booleans can be quoted.
				quoted := false
				if opts.Contains("string") {
					switch ft.Kind() {
					case reflect.Bool,
						reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
						reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr,
						reflect.Float32, reflect.Float64,
						reflect.String:
						quoted = true
					}
				}

				// Record found field and index sequence.
				if name != "" || !sf.Anonymous || ft.Kind() != reflect.Struct {
					tagged := name != ""
					if name == "" {
						name = sf.Name
					}
					field := field{
						name:      name,
						tag:       tagged,
						index:     index,
						typ:       ft,
						omitEmpty: opts.Contains("omitempty"),
						quoted:    quoted,
					}
					field.nameBytes = []byte(field.name)
					field.equalFold = foldFunc(field.nameBytes)

					// Build nameEscHTML and nameNonEsc ahead of time.
					nameEscBuf.Reset()
					nameEscBuf.WriteString(`"`)
					HTMLEscape(&nameEscBuf, field.nameBytes)
					nameEscBuf.WriteString(`":`)
					field.nameEscHTML = nameEscBuf.String()
					field.nameNonEsc = `"` + field.name + `":`

					fields = append(fields, field)
					if count[f.typ] > 1 {
						// If there were multiple instances, add a second,
						// so that the annihilation code will see a duplicate.
						// It only cares about the distinction between 1 or 2,
						// so don't bother generating any more copies.
						fields = append(fields, fields[len(fields)-1])
					}
					continue
				}

				// Record new anonymous struct to explore in next round.
				nextCount[ft]++
				if nextCount[ft] == 1 {
					next = append(next, field{name: ft.Name(), index: index, typ: ft})
				}
			}
		}
	}

	sort.Slice(fields, func(i, j int) bool {
		x := fields
		// sort field by name, breaking ties with depth, then
		// breaking ties with "name came from json tag", then
		// breaking ties with index sequence.
		if x[i].name != x[j].name {
			return x[i].name < x[j].name
		}
		if len(x[i].index) != len(x[j].index) {
			return len(x[i].index) < len(x[j].index)
		}
		if x[i].tag != x[j].tag {
			return x[i].tag
		}
		return byIndex(x).Less(i, j)
	})

	// Delete all fields that are hidden by the Go rules for embedded fields,
	// except that fields with JSON tags are promoted.

	// The fields are sorted in primary order of name, secondary order
	// of field index length. Loop over names; for each name, delete
	// hidden fields by choosing the one dominant field that survives.
	out := fields[:0]
	for advance, i := 0, 0; i < len(fields); i += advance {
		// One iteration per name.
		// Find the sequence of fields with the name of this first field.
		fi := fields[i]
		name := fi.name
		for advance = 1; i+advance < len(fields); advance++ {
			fj := fields[i+advance]
			if fj.name != name {
				break
			}
		}
		if advance == 1 { // Only one field with this name
			out = append(out, fi)
			continue
		}
		dominant, ok := dominantField(fields[i : i+advance])
		if ok {
			out = append(out, dominant)
		}
	}

	fields = out
	sort.Sort(byIndex(fields))

	// for i := range fields {
	// 	f := &fields[i]
	// 	f.encoder = typeEncoder(typeByIndex(t, f.index))
	// }
	nameIndex := make(map[string]int, len(fields))
	for i, field := range fields {
		nameIndex[field.name] = i
	}
	return structFields{fields, nameIndex}
}

// dominantField looks through the fields, all of which are known to
// have the same name, to find the single field that dominates the
// others using Go's embedding rules, modified by the presence of
// JSON tags. If there are multiple top-level fields, the boolean
// will be false: This condition is an error in Go and we skip all
// the fields.
func dominantField(fields []field) (field, bool) {
	// The fields are sorted in increasing index-length order, then by presence of tag.
	// That means that the first field is the dominant one. We need only check
	// for error cases: two fields at top level, either both tagged or neither tagged.
	if len(fields) > 1 && len(fields[0].index) == len(fields[1].index) && fields[0].tag == fields[1].tag {
		return field{}, false
	}
	return fields[0], true
}

var fieldCache sync.Map // map[reflect.Type]structFields

// cachedTypeFields is like typeFields but uses a cache to avoid repeated work.
func cachedTypeFields(t reflect.Type) structFields {
	if f, ok := fieldCache.Load(t); ok {
		return f.(structFields)
	}
	f, _ := fieldCache.LoadOrStore(t, typeFields(t))
	return f.(structFields)
}

// indirect walks down v allocating pointers as needed,
// until it gets to a non-pointer.
// If it encounters an Unmarshaler, indirect stops and returns that.
// If decodingNull is true, indirect stops at the first settable pointer so it
// can be set to nil.
func indirect(v reflect.Value, decodingNull bool) (json.Unmarshaler, encoding.TextUnmarshaler, reflect.Value) {
	// Issue #24153 indicates that it is generally not a guaranteed property
	// that you may round-trip a reflect.Value by calling Value.Addr().Elem()
	// and expect the value to still be settable for values derived from
	// unexported embedded struct fields.
	//
	// The logic below effectively does this when it first addresses the value
	// (to satisfy possible pointer methods) and continues to dereference
	// subsequent pointers as necessary.
	//
	// After the first round-trip, we set v back to the original value to
	// preserve the original RW flags contained in reflect.Value.
	v0 := v
	haveAddr := false

	// If v is a named type and is addressable,
	// start with its address, so that if the type has pointer methods,
	// we find them.
	if v.Kind() != reflect.Ptr && v.Type().Name() != "" && v.CanAddr() {
		haveAddr = true
		v = v.Addr()
	}
	for {
		// Load value from interface, but only if the result will be
		// usefully addressable.
		if v.Kind() == reflect.Interface && !v.IsNil() {
			e := v.Elem()
			if e.Kind() == reflect.Ptr && !e.IsNil() && (!decodingNull || e.Elem().Kind() == reflect.Ptr) {
				haveAddr = false
				v = e
				continue
			}
		}

		if v.Kind() != reflect.Ptr {
			break
		}

		if decodingNull && v.CanSet() {
			break
		}

		// Prevent infinite loop if v is an interface pointing to its own address:
		//     var v interface{}
		//     v = &v
		if v.Elem().Kind() == reflect.Interface && v.Elem().Elem() == v {
			v = v.Elem()
			break
		}
		if v.IsNil() {
			v.Set(reflect.New(v.Type().Elem()))
		}
		if v.Type().NumMethod() > 0 && v.CanInterface() {
			if u, ok := v.Interface().(json.Unmarshaler); ok {
				return u, nil, reflect.Value{}
			}
			if !decodingNull {
				if u, ok := v.Interface().(encoding.TextUnmarshaler); ok {
					return nil, u, reflect.Value{}
				}
			}
		}

		if haveAddr {
			v = v0 // restore original value after round-trip Value.Addr().Elem()
			haveAddr = false
		} else {
			v = v.Elem()
		}
	}
	return nil, nil, v
}

type ODBCRecordset struct {
	MetaDataWork
	db   *sql.DB
	err  error
	rows *sql.Rows
	conn *sql.Conn

	result sql.Result

	ctx context.Context

	cols []string
	vals []interface{}
}

func NewODBCRecordset() ODBCRecordset {
	var r ODBCRecordset = *new(ODBCRecordset)
	r.MetaDataWork = NewMetaDataWork()
	r.db = nil
	r.rows = nil

	return r
}

func (t *ODBCRecordset) Connection(connString string) error {

	//	t.db, t.err = sql.Open("sqlserver", connString)
	//	if t.err != nil {
	//		//log.Fatal("Error creating connection pool: ", err.Error())
	//		return t.err
	//	}
	connector, err := mssql.NewConnector(connString)
	if err != nil {
		return err
	}
	connector.SessionInitSQL = "SET ANSI_NULLS ON"
	t.db = sql.OpenDB(connector)

	t.ctx = context.Background()
	err = t.db.PingContext(t.ctx)
	if err != nil {
		return err
	}

	t.conn, err = t.db.Conn(t.ctx)
	if err != nil {
		return err
	}

	return nil
}

func (t *ODBCRecordset) AttachFromSQL(db *sql.DB, FirmaID int) error {
	e := t.MetaDataWork.AttachFromSQL(db, FirmaID)
	if e != nil {
		return e
	}

	db.Close()

	connString := t.MetaDataWork.GetConnectString()
	connector, err := mssql.NewConnector(connString)
	if err != nil {
		return err
	}
	connector.SessionInitSQL = "SET ANSI_NULLS ON"
	t.db = sql.OpenDB(connector)

	t.ctx = context.Background()
	err = t.db.PingContext(t.ctx)
	if err != nil {
		return err
	}

	t.conn, err = t.db.Conn(t.ctx)
	if err != nil {
		return err
	}

	// t.db = sql.OpenDB(connector)
	// if t.err != nil {
	// 	//log.Fatal("Error creating connection pool: ", err.Error())
	// 	return t.err
	// }

	return nil
}

func (t *ODBCRecordset) AttachMD(fileName string) error {
	t.MetaDataWork.AttachMD(fileName)

	connString := t.MetaDataWork.GetConnectString()
	connector, err := mssql.NewConnector(connString)
	if err != nil {
		return err
	}
	t.db = sql.OpenDB(connector)

	connector.SessionInitSQL = "SET ANSI_NULLS ON"
	t.ctx = context.Background()
	err = t.db.PingContext(t.ctx)
	if err != nil {
		return err
	}

	t.conn, err = t.db.Conn(t.ctx)
	if err != nil {
		return err
	}

	// t.db = sql.OpenDB(connector)
	// if t.err != nil {
	// 	//log.Fatal("Error creating connection pool: ", err.Error())
	// 	return t.err
	// }

	return nil
}

func (t *ODBCRecordset) Close() error {
	if t.rows != nil {
		t.err = t.rows.Close()
		t.rows = nil
	}
	if t.err != nil {
		return t.err
	}
	if t.conn != nil {
		t.conn.Close()
		t.conn = nil
	}
	if t.db != nil {
		t.err = t.db.Close()
		t.db = nil
	}

	return t.err
}

func (t *ODBCRecordset) BeginTx() (*sql.Tx, error) {

	opts := &sql.TxOptions{
		Isolation: sql.LevelSerializable,
	}

	txn, err := t.conn.BeginTx(t.ctx, opts)

	return txn, err
}

func (t *ODBCRecordset) Execute(q string) error {
	var err error
	q, err = t.MetaDataWork.ParseQuery(q)
	if err != nil {
		return err
	}
	t.result, t.err = t.conn.ExecContext(t.ctx, q)

	return t.err
}

func (t *ODBCRecordset) RowsAffected() int64 {
	m, err := t.result.RowsAffected()
	if err != nil {
		return -1
	}

	return m
}

func (t *ODBCRecordset) Exec(q string) error {
	t.err = nil
	if t.rows != nil {
		t.err = t.rows.Close()
		t.rows = nil
	}
	if t.err != nil {
		return t.err
	}

	//ctx := context.Background()
	t.err = t.db.PingContext(t.ctx)
	if t.err != nil {
		return t.err
	}

	q, t.err = t.MetaDataWork.ParseQuery(q)
	if t.err != nil {
		return t.err
	}
	//	t.rows, t.err = t.db.QueryContext(t.ctx, q)
	t.rows, t.err = t.conn.QueryContext(t.ctx, q)
	if t.err != nil {

		fmt.Println(q)
		fmt.Println(t.err)

		return t.err
	}

	t.cols, t.err = t.rows.Columns()
	if t.err != nil {
		return t.err
	}

	if t.cols == nil {
		return nil
	}
	t.vals = make([]interface{}, len(t.cols))
	// for i := 0; i < len(t.cols); i++ {
	// 	t.vals[i] = new(interface{})
	// }

	return t.err
}

type rowAbstract map[string]interface{}
type RowAbstract map[string]interface{}

func (t ODBCRecordset) GetRows() ([]RowAbstract, error) {
	//masterData := make(map[string][]interface{})
	masterData := make([]RowAbstract, 0) //[]RowAbstract{}
	var err error
	cols, _ := t.rows.Columns()
	lenCols := len(cols)
	rawResult := make([]interface{}, lenCols)
	dest := make([]interface{}, lenCols) // A temporary any slice
	for i := range t.vals {
		dest[i] = &rawResult[i] // Put pointers to each string in the interface slice
	}

	for t.rows.Next() {
		err = t.rows.Scan(dest...)
		if err != nil {
			return nil, err
		}
		//result := make(map[string]interface{}, len(t.cols))
		result := make(RowAbstract, len(t.cols))
		for i, raw := range rawResult {
			//for i, v := range t.vals {

			//masterData[t.cols[i]] = append(masterData[t.cols[i]], v[0])
			result[t.cols[i]] = raw

			// x := v.([]byte)
			// if nx, ok := strconv.ParseFloat(string(x), 64); ok == nil {
			//     masterData[t.cols[i]] = append(masterData[t.cols[i]], nx)
			// } else if b, ok := strconv.ParseBool(string(x)); ok == nil {
			//     masterData[t.cols[i]] = append(masterData[t.cols[i]], b)
			// } else if "string" == fmt.Sprintf("%T", string(x)) {
			//     masterData[t.cols[i]] = append(masterData[t.cols[i]], string(x))
			// } else {
			//     fmt.Printf("Failed on if for type %T of %v\n", x, x)
			// }
		}
		masterData = append(masterData, result)
	}

	return masterData, err
}
func (t *ODBCRecordset) NextResultSet() bool {

	b := t.rows.NextResultSet()
	if b {

		t.cols, t.err = t.rows.Columns()
		if t.err != nil {
			return false
		}

		if t.cols == nil {
			return false
		}
		t.vals = make([]interface{}, len(t.cols))
		// for i := 0; i < len(t.cols); i++ {
		// 	t.vals[i] = new(interface{})
		// }

	}

	return b
}

func (t ODBCRecordset) ToJson() ([]byte, error) {
	var buf []byte
	var err error

	//	results := []map[string]string{}
	//var results []byte
	cols, _ := t.rows.Columns()
	lenCols := len(cols)

	rawResult := make([]interface{}, lenCols)

	dest := make([]interface{}, lenCols) // A temporary any slice
	for i := range rawResult {
		dest[i] = &rawResult[i] // Put pointers to each string in the interface slice
	}

	buffer := new(bytes.Buffer)

	for t.rows.Next() {
		//result := make(map[string]interface{}, lenCols)
		t.rows.Scan(dest...)
		buffer.WriteString("{\n")
		for i, raw := range rawResult {
			if raw == nil {
				continue
				//result[cols[i]] = ""
				buffer.WriteString(fmt.Sprintf(`"%s": ""`, cols[i]))
				if i < (lenCols - 1) {
					buffer.WriteString(",")
				}
				buffer.WriteString("\n")
			} else {
				//				result[cols[i]] = string(raw)
				//result[cols[i]] = raw
				switch t := raw.(type) {
				case int64:
					buffer.WriteString(fmt.Sprintf(`"%s": %d`, cols[i], t))
				case int32:
					buffer.WriteString(fmt.Sprintf(`"%s": %d`, cols[i], t))
				case int16:
					buffer.WriteString(fmt.Sprintf(`"%s": %d`, cols[i], t))
				case float64:

					var buf [8]byte
					n := math.Float64bits(t)
					buf[0] = byte(n >> 56)
					buf[1] = byte(n >> 48)
					buf[2] = byte(n >> 40)
					buf[3] = byte(n >> 32)
					buf[4] = byte(n >> 24)
					buf[5] = byte(n >> 16)
					buf[6] = byte(n >> 8)
					buf[7] = byte(n)
					buffer.WriteString(fmt.Sprintf(`"%s": %f`, cols[i], t))
				case float32:
					buffer.WriteString(fmt.Sprintf(`"%s": %f`, cols[i], t))
				case time.Time:
					buffer.WriteString(fmt.Sprintf(`"%s": %s`, cols[i], fmt.Sprintf(`"%s"`, t.Format("2006-01-02 15:04:05"))))
				case string:
					// t = strings.Replace(t, `"`, `""`, -1)
					// t = strings.Replace(t, "\n", "\\n", -1)
					// t = strings.Replace(t, "\t", "\\t", -1)
					//t = strings.Replace(t, "\\\\", "\\", -1)
					b, _ := json.Marshal(t)
					buffer.WriteString(fmt.Sprintf(`"%s": %s`, cols[i], string(b)))
				case bool:
					if t {
						buffer.WriteString(fmt.Sprintf(`"%s": true`, cols[i]))
					} else {
						buffer.WriteString(fmt.Sprintf(`"%s": false`, cols[i]))
					}
				case []uint8:
					/*
						var b []byte = make([]byte, 8)
						bytes := []byte(t)
						for i := 0; i < len(bytes); i++ {
							b[i] = bytes[i]
						}
						bits := binary.LittleEndian.Uint64(b)
						float := math.Float64frombits(bits)
					*/

					//fmt.Println(string(t))
					//fmt.Printf("%d %s\n", len(t), string(t))

					// var b []byte = make([]byte, 8)
					// k := 0
					// for i := len(t) - 1; i >= 0; i-- {
					// 	b[k] = t[i]
					// 	k++
					// }
					// bits := binary.LittleEndian.Uint64(b)
					// float := math.Float64frombits(bits)
					//float, err := strconv.ParseFloat(string(t))
					//buffer.WriteString(fmt.Sprintf(`"%s": %f.%d`, cols[i], float, t[4]))
					buffer.WriteString(fmt.Sprintf(`"%s": %s`, cols[i], string(t)))
					//				case bool:
					//					if t {
					//						buffer.WriteString(fmt.Sprintf(`"%s": true`, cols[i]))
					//					} else {
					//						buffer.WriteString(fmt.Sprintf(`"%s": false`, cols[i]))
					//					}
				default:
					log.Println(raw, reflect.TypeOf(raw))
				}
				if i < (lenCols - 1) {
					buffer.WriteString(",")
				}
				buffer.WriteString("\n")
			}
		}
		str := strings.Trim(string(buffer.Bytes()), " \n")
		if string(str[len(str)-1]) == "," {
			str = str[:len(str)-1] // удаляем последний символ
		}
		buffer = new(bytes.Buffer)
		buffer.WriteString(str)
		buffer.WriteString("},\n")
	}
	str := string(buffer.Bytes())
	str0 := "["
	if len(str) >= 2 {
		str0 += str[0:len(str)-2] + "\n"

	}
	str0 += "]"
	buf = []byte(str0)

	return buf, err
}

func setValuesStruct(item reflect.Value, data RowAbstract) (err error) {

	typeName := item.Type().String() //getTypeName(obj)

	var fields structFields

	t := item.Type()
	fields = cachedTypeFields(t)

	for key, value := range data {
		field := item.FieldByName(key)
		if !field.IsValid() {
			nFld, ok := fields.nameIndex[key]
			if !ok {
				continue
			}
			field = item.FieldByIndex([]int{nFld})
			if !field.IsValid() {
				continue
			}
		}

		//fmt.Printf("%s  %s\n", reflect.TypeOf(value).String(), field.Type().String())

		if reflect.TypeOf(value).String() == "time.Time" && field.Type().String() == "MetaDataWork.ShortDate" {
			var tt ShortDate
			tt.Time = value.(time.Time) //.In(GetLocation())
			field.Set(reflect.ValueOf(tt))
			continue
		}
		if field.Type().String() != reflect.TypeOf(value).String() {
			err = fmt.Errorf("cannot unmarshal %s into Go struct field %s.%s of type %s", reflect.TypeOf(value).String(), typeName, key, field.Type().String())
			return
		}

		field.Set(reflect.ValueOf(value))
	}

	return
}

// func setValuesFromMapArray(obj interface{}, data []map[string]interface{}) {
func setValuesFromMapArray(obj interface{}, data []RowAbstract) (err error) {

	v := reflect.ValueOf(obj) //.Elem()
	//fmt.Println(v.Kind())

	_, ut, pv := indirect(v, false)
	// u, ut, pv := indirect(v, false)
	// if u != nil {
	// 	return u.UnmarshalJSON(d.data[start:d.off])
	// }
	if ut != nil {
		e := json.UnmarshalTypeError{Value: "object", Type: v.Type(), Offset: 0}
		if e.Struct != "" || e.Field != "" {
			return fmt.Errorf("json: cannot unmarshal " + e.Value + " into Go struct field " + e.Struct + "." + e.Field + " of type " + e.Type.String())
		}
		return fmt.Errorf("json: cannot unmarshal " + e.Value + " into Go value of type " + e.Type.String())
		//			 return nil
	}
	//	fmt.Println(u)
	//	fmt.Println(ut)

	v = pv
	//	fmt.Println(v.Kind())
	//typeName := v.Name()

	ii := len(data)
	if v.Kind() == reflect.Slice {
		if ii >= v.Cap() {
			newcap := v.Cap() + v.Cap()/2
			if newcap < ii {
				newcap = ii
			}
			if newcap < ii {
				newcap = ii
			}
			newv := reflect.MakeSlice(v.Type(), v.Len(), newcap)
			reflect.Copy(newv, v)
			v.Set(newv)
		}
		if ii >= v.Len() {
			v.SetLen(ii)
		}
	} else {
		err = fmt.Errorf("Приёмник - не массив")
		return
	}

	// var fields structFields

	// switch v.Index(0).Kind() {
	// case reflect.Struct:
	// 	t := v.Index(0).Type()
	// 	fields = cachedTypeFields(t)
	// }
	for i := 0; i < ii; i++ {
		item := v.Index(i)

		err = setValuesStruct(item, data[i])
		//for key, value := range data[i] {

		// field := item.FieldByName(key)
		// if !field.IsValid() {
		// 	nFld, ok := fields.nameIndex[key]
		// 	if !ok {
		// 		continue
		// 	}
		// 	field = item.FieldByIndex([]int{nFld})
		// 	if !field.IsValid() {
		// 		continue
		// 	}
		// }

		// if field.Type().String() != reflect.TypeOf(value).String() {
		// 	fmt.Printf("cannot unmarshal %s into Go struct field %s.%s of type %s", reflect.TypeOf(value).String(), typeName, key, field.Type().String())
		// 	continue
		// }

		// field.Set(reflect.ValueOf(value))
		//}
	}
	//	fmt.Println(fields)
	return
}

// --
// func (t ODBCRecordset) _UnMarshal(obj interface{}, data any) (err error) {
func (t *ODBCRecordset) UnMarshalNew(obj any) (err error) {
	data, err := t.GetRows()
	if err != nil {
		return
	}

	v := reflect.ValueOf(obj) //.Elem()
	if v.Kind() != reflect.Pointer {
		err = fmt.Errorf("_UnMarshal: Параметр д.б. указатель")
		return
	}
	v = v.Elem()
	if (v.Kind() == reflect.Array) || (v.Kind() == reflect.Slice) {
		return setValuesFromMapArray(obj, data)
	} else if v.Kind() == reflect.Struct {
		return setValuesStruct(v, data[0])
	}

	//switch vv := data.(type) {
	//case []RowAbstract:
	//fmt.Println("vv=", vv)
	var dat any
	p := data[0]
	for _, el := range p {
		dat = el
		break
	}
	//default:
	//	fmt.Println("vv=", vv)
	//}

	z := reflect.ValueOf(dat)
	//	if v.Type().String() != reflect.TypeOf(v).String() {
	if v.Type().String() != z.Type().String() {
		err = fmt.Errorf("cannot unmarshal into Go struct field %s of type %s", z.Type().String(), v.Type().String())
		return
	}

	v.Set(reflect.ValueOf(data))

	return
}

func (t ODBCRecordset) GetValue(obj interface{}, data any, f string) (err error) {

	v := reflect.ValueOf(obj) //.Elem()
	if v.Kind() != reflect.Pointer {
		err = fmt.Errorf("GetValue: Параметр д.б. указатель")
		return
	}
	v = v.Elem()
	if (v.Kind() == reflect.Array) || (v.Kind() == reflect.Slice) {
		err = fmt.Errorf("GetValue: Параметр д.б. не массиворм и не структурой")
		return
	} else if v.Kind() == reflect.Struct {
		err = fmt.Errorf("GetValue: Параметр д.б. не массиворм и не структурой")
		return
	}

	switch vv := data.(type) {
	case []RowAbstract:
		//fmt.Println("vv=", vv)
		p := vv[0]
		found := false
		for key, el := range p {
			if key != f {
				continue
			}
			data = el
			found = true
			break
		}
		if !found {
			err = fmt.Errorf("GetValue: не найдено поле '%s'", f)
			return
		}
	default:
		err = fmt.Errorf("GetValue: Не верный тип данных источника")
		return
	}

	z := reflect.ValueOf(data)
	//	if v.Type().String() != reflect.TypeOf(v).String() {
	if v.Type().String() != z.Type().String() {
		err = fmt.Errorf("cannot unmarshal into Go struct field %s of type %s", z.Type().String(), v.Type().String())
		return
	}

	v.Set(reflect.ValueOf(data))

	return

}

func (t ODBCRecordset) UnMarshal(obj interface{}, data any) (err error) {

	v := reflect.ValueOf(obj) //.Elem()
	if v.Kind() != reflect.Pointer {
		err = fmt.Errorf("_UnMarshal: Параметр д.б. указатель")
		return
	}
	v = v.Elem()
	if (v.Kind() == reflect.Array) || (v.Kind() == reflect.Slice) {
		return setValuesFromMapArray(obj, data.([]RowAbstract))
	} else if v.Kind() == reflect.Struct {
		return setValuesStruct(v, data.([]RowAbstract)[0])
	}

	switch vv := data.(type) {
	case []RowAbstract:
		//fmt.Println("vv=", vv)
		p := vv[0]
		for _, el := range p {
			data = el
			break
		}
	default:
		fmt.Println("vv=", vv)
	}

	z := reflect.ValueOf(data)
	//	if v.Type().String() != reflect.TypeOf(v).String() {
	if v.Type().String() != z.Type().String() {
		err = fmt.Errorf("cannot unmarshal into Go struct field %s of type %s", z.Type().String(), v.Type().String())
		return
	}

	v.Set(reflect.ValueOf(data))

	return
}

func (t ODBCRecordset) GetCols() []string {
	return t.cols
}

func (t *ODBCRecordset) Next() (bool, error) {
	r := t.rows.Next()
	if r {
		cols, _ := t.rows.Columns()
		lenCols := len(cols)

		rawResult := make([]interface{}, lenCols)

		dest := make([]interface{}, lenCols) // A temporary any slice
		for i := range rawResult {
			dest[i] = &rawResult[i] // Put pointers to each string in the interface slice
		}
		t.rows.Scan(dest...)
		for i, raw := range rawResult {
			t.vals[i] = raw
		}
		//t.err = t.rows.Scan(t.vals...)
	}
	if t.rows.Err() != nil {
		return r, t.rows.Err()
	}

	return r, t.err
}

func (t ODBCRecordset) GetValueByName(name string) (interface{}, error) {
	var v interface{}
	var err error
	var i int

	err = nil
	for i = 0; i < len(t.cols); i++ {
		//t.vals[i] = new(interface{})
		if strings.ToUpper(t.cols[i]) == strings.ToUpper(name) {
			// //v = t.vals[i]
			// _pval := t.vals[i]
			// pval := _pval.(*interface{})
			// return (*pval), nil
			return t.vals[i], nil
			//	break
		}
	}
	if i >= len(t.cols) {
		err = fmt.Errorf("Поле %s не найдено", name)
	}

	return v.(*interface{}), err

}

func (t ODBCRecordset) GetStringByName(name string) (string, error) {
	//var _pval interface{}
	var err error
	var i int

	s := ""

	err = nil
	for i = 0; i < len(t.cols); i++ {
		//t.vals[i] = new(interface{})
		if strings.ToUpper(t.cols[i]) == strings.ToUpper(name) {
			//_pval = t.vals[i]
			//pval := _pval.(*interface{})
			switch v := t.vals[i].(type) {
			case nil:
				s = "NULL"
			case bool:
				if v {
					s = "1"
				} else {
					s = "0"
				}
			case []byte:
				s = fmt.Sprint(string(v))
			case int, int8, int16, int32, int64:
				s = fmt.Sprintf("%d", v)
			case float32, float64:
				s = fmt.Sprintf("%f", v)
			case time.Time:
				s = fmt.Sprint(v.Format("2006-01-02 15:04:05.999"))
			default:
				s = fmt.Sprint(v)
			}

			break
		}
	}
	if i >= len(t.cols) {
		err = fmt.Errorf("Поле %s не найдено", name)
	}

	return s, err

}

// Find возвращает наименьший индекс i,
// при котором x == a[i],
// или len(a), если такого индекса нет.
func Find(a []string, x string) int {
	for i, n := range a {
		if x == n {
			return i
		}
	}
	return len(a)
}

// Contains указывает, содержится ли x в a.
func Contains(a []string, x string) bool {
	for _, n := range a {
		if x == n {
			return true
		}
	}
	return false
}
