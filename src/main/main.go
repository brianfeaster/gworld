package main

import (
	"fmt"
	//"time" time.Sleep(100 * time.Millisecond)
	"bytequeue"
	"strconv"
	"bufio"
	"os"
)

///////////////////////////////////////////////////////////////////////////////

/* Scheme Scanner

   Need to implement pairs, vectors, symbols, strings, numbers, characters, atomics
*/

// States
var A byte = 0 // Start
var B byte = 1 // Integer
var C byte = 2 // Symbol
var D byte = 3 // Integer or Symbol
var E byte = 4 // String
var F byte = 5 // String escape
var G byte = 6 // Hash
var H byte = 7 // Character

// Final states with unget
var b byte = 128 + 0 // Final integer
var c byte = 128 + 1 // Final symbol

// Final states
var n byte = 128 + 64 + 0 // Final string
var o byte = 128 + 64 + 1 // Final paren open
var p byte = 128 + 64 + 2 // Final paren close
var q byte = 128 + 64 + 3 // Quote
var r byte = 128 + 64 + 4 // Vector open
var s byte = 128 + 64 + 5 // Character

var InitialState byte = A
var FirstFinalStateUnget byte = b
var FirstFinalState byte = n

// Helpers //

func StateString(state byte) string {
	switch state {
	case A:
		return "start"
	case B:
		return "int"
	case C:
		return "sym"
	case D:
		return "int or sym"
	case E:
		return "str"
	case F:
		return "str esc chr"
	case G:
		return "hash"
	case H:
		return "character"

	case b:
		return "final int"
	case c:
		return "final sym"

	case n:
		return "final str"
	case o:
		return "final paren open"
	case p:
		return "final paren close"
	case q:
		return "final quote"
	case r:
		return "final vector open"
	case s:
		return "final character"
	}
	return "unknown state"
}

func StateIsFinal(state byte) bool {
	return FirstFinalStateUnget <= state
}

func FinalStateShouldUnget(state byte) bool {
	return state < FirstFinalState
}

var Transition_A = [256]byte{ // Initial
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ A, C, E, G, C, C, C, q, o, p, C, D, A, D, A, C, B, B, B, B, B, B, B, B, B, B, C, A, C, C, C, C,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, o, C, p, C, C,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ A, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, o, C, p, C, A,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ A, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C}

var Transition_B = [256]byte{ // Integer
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, B, B, B, B, B, B, B, B, B, B, b, b, b, b, b, b,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b}

var Transition_C = [256]byte{ // Symbol
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ c, C, c, c, C, C, C, c, c, c, C, C, c, C, c, C, C, C, C, C, C, C, C, C, C, C, C, c, C, C, C, C,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, c, C, c, C, C,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ c, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, c, C, c, C, c,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ c, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C}

var Transition_D = [256]byte{ // Integer or Symbol
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ c, C, c, c, C, C, C, c, c, c, C, C, c, C, c, C, B, B, B, B, B, B, B, B, B, B, C, c, C, C, C, C,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, c, C, c, C, C,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ c, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, c, C, c, C, c,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ c, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C}

var Transition_E = [256]byte{ // String
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ E, E, n, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E}

var Transition_F = [256]byte{ // String escape
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E}

var Transition_G = [256]byte{ // Hash
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ A, A, A, A, A, A, A, A, r, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, r, H, A, A, A,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, r, A, A, A, A,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A, A}

var Transition_H = [256]byte{ // Character
	//  ^@ ^A ^B ^C ^D ^E ^F \a \b \t \n \v \f \r ^N ^O ^P ^Q ^R ^S ^T ^U ^V ^W ^X ^Y ^Z ^[ ^\ ^] ^^ ^_
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//      !  "  #  $  %  &  '  (  )  *  +  ,  -  .  /  0  1  2  3  4  5  6  7  8  9  :  ;  <  =  >  ?
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//   @  A  B  C  D  E  F  G  H  I  J  K  L  M  N  O  P  Q  R  S  T  U  V  W  X  Y  Z  [  \  ]  ^  _
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//   `  a  b  c  d  e  f  g  h  i  j  k  l  m  n  o  p  q  r  s  t  u  v  w  x  y  z  {  |  }  ~ ^?
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//  ~@ ~A ~B ~C ~D ~E ~F ~G ~H ~I ~J ~K ~L ~M ~N ~O ~P ~Q ~R ~S ~T ~U ~V ~W ~X ~Y ~Z ~[ ~\ ~] ~^ ~_
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//  ~   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//    .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s,
	//   .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .  .
	/**/ s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s}

var TransitionTable = [...][256]byte{
	Transition_A,
	Transition_B,
	Transition_C,
	Transition_D,
	Transition_E,
	Transition_F,
	Transition_G,
	Transition_H,
}

func transition(state byte, chr byte) byte {
	return TransitionTable[state][chr]
}

func scan(conn *bytequeue.ByteQueue) (state byte) {
	state = InitialState

	for !StateIsFinal(state) {
		if state == A {
			conn.TokenClear() // Always reset scanned token string on initial state
		}
		state = transition(state, conn.Get())
	}

	if FinalStateShouldUnget(state) {
		conn.Unget()
	}

	return
}

///////////////////////////////////////////////////////////////////////////////

/* Scheme Objects
 */

type stype interface{} // Base scheme object type

type stvector []stype

type stpair struct {
	car interface{}
	cdr interface{}
}
type stchar byte
type stint int
type ststring []byte
type stsymbol string
type stnull string

// Static atoms and symbols
var sonull stnull = stnull("()")
var sonullvec stvector = stvector{}
var sonullstring ststring = ststring("")
var soquote stsymbol = stsymbol("quote")

///////////////////////////////////////////////////////////////////////////////

/* Scheme parser
 */

type Parser struct {
	conn *bytequeue.ByteQueue
}

func ParserNew(q *bytequeue.ByteQueue) *Parser {
	if nil == q {
		fmt.Println("Invalid bytequeue.ByteQueue")
		return nil
	}
	return &Parser{q}
}

/* Determine length of a proper scheme list
*/
func objListLength(l stype) (len int) {
	for len = 0; ; l = l.(stpair).cdr {
		switch l.(type) {
		case stpair:
			len++
		default:
			return
		}
	}
}

/* Copy proper scheme list into a new scheme vector
*/
func listToVector(l stype) (v stvector) {
	len := objListLength(l)
	if 0 == len {
		v = sonullvec
	} else {
		v = make(stvector, len, len)
		for i:=0; i<len; i++ {
			v[i] = l.(stpair).car
			l = l.(stpair).cdr
		}
	}
	return
}

func (this *Parser) parse(list bool) interface{} {
	var ret interface{} = nil
	//var s spair = spair{sint(1), spair{sint(2), sstring("meow")}}
	//display(s, false)

	var finalState byte = scan(this.conn)
	//fmt.Printf("{%d}", finalState) // Print the state ID

	switch finalState {
	//case b : ret = func (s int, e error) sint { return sint(s) }(strconv.Atoi(this.conn.Token()))
	case b:
		ret, _ = strconv.Atoi(this.conn.Token())
		ret = stint(ret.(int))
	case c:
		ret = stsymbol(this.conn.Token())
	case n:
		ret = ststring(this.conn.Token())
	case o:
		ret = this.parse(true)
	case p:
		ret = sonull
		if list {
			return ret
		}
	case q:
		ret = this.parse(false)
		ret = stpair{ret, sonull}
		ret = stpair{soquote, ret}
	case r:
		ret = this.parse(true) // First parse syntatically as a list then copy to vector
		ret = listToVector(ret)
	case s:
		ret = stchar(this.conn.Token()[2])
	default:
		ret = stsymbol(this.conn.Token())
	}

	if list {
		return stpair{ret, this.parse(true)}
	} else {
		return ret
	}
	//fmt.Printf("  [%-20s] \"%s\"\n", StateString(finalState), this.conn.Token())
}

func display(s stype, list bool) {
	switch s.(type) {
	case stpair:
		if !list {
			fmt.Print("(")
		}
		display(s.(stpair).car, false)
		switch s.(stpair).cdr.(type) {
		case stpair:
			fmt.Print(" ")
		default:
			if s.(stpair).cdr != sonull {
				fmt.Print(" . ")
			}
		}
		display(s.(stpair).cdr, true)
		if !list {
			fmt.Print(")")
		}
	case stvector:
		fmt.Print("#(")
		for i, o := range s.(stvector) {
			display(o, false)
			if i == len(s.(stvector))-1 {
				fmt.Print(")")
			} else {
				fmt.Print(" ")
			}
		}
	case stint:
		fmt.Printf("%d", s)
	case stsymbol:
		fmt.Printf("%s", s)
	case ststring:
		fmt.Printf("%s", s)
	case stnull:
		if !list {
			fmt.Printf("()")
		}
	case stchar:
		fmt.Printf("#\\%c", s.(stchar))
	default:
		fmt.Printf("#<%p>", s)
	}
}

func parseLoop (parser *Parser) {
	for {
		display(parser.parse(false), false)
		fmt.Println()
	}
}

///////////////////////////////////////////////////////////////////////////////

func main() {
	var conn *bytequeue.ByteQueue = bytequeue.ConnQueueNew()
	var parser *Parser = ParserNew(conn) // Give it a character stream
	if nil == parser {
		fmt.Println("Can not create parser object")
		return
	}

	go parseLoop(parser)

	conn.Conn.Write([]byte("(entity 60 \"GO\" #(0 15 \\G 0 11 #\\o) (1 3460 2767))"))
	scanner := bufio.NewScanner(os.Stdin)
	for scanner.Scan() {
		t := []byte(scanner.Text())
		for i, c := range t {
			if c == '"' { t[i] = '\'' }
		}
		conn.Conn.Write([]byte("(voice 60 20 \"" + string(t) + "\")"))
	}
	//parser.parse()
}

///////////////////////////////////////////////////////////////////////////////
