import Lean

namespace LeanModel.Constants

def bpsDenom : UInt64 := 10000
def bpsMaxRem : UInt64 := 9999
def u64ModBpsQuot : UInt64 := 1844674407370955
def u64ModBpsRem : UInt64 := 1616
def rebateDivisor : UInt64 := 10
def makerRebateCapDivisor : UInt64 := 5
def treasuryCutDivisor : UInt64 := 4
def flashDenom : UInt64 := 5000
def flashMaxRem : UInt64 := 4999
def u64ModFlashQuot : UInt64 := 3689348814741910
def u64ModFlashRem : UInt64 := 1616
def institutionalBandMin : UInt64 := 10000000000000

def mg10Divisor : UInt64 := 0x8003
def mg10Reciprocal : UInt64 := 0xFFF4
def limbMask : UInt64 := 0xFFFF
def subBias : UInt64 := 0xC0000000
def blobGasPerSlot : UInt64 := 131072

def l8Mask : UInt64 := 0x0101010101010101
def h8Mask : UInt64 := 0x8080808080808080
def m16Mask : UInt64 := 0x00FF00FF00FF00FF
def l16Mask : UInt64 := 0x0001000100010001
def calldataNzByteShift : UInt64 := 8

def babyBearP : UInt64 := 2013265921
def babyBearMu : UInt64 := 2281701377
def limbBase : UInt64 := 4294967296
def low32Mask : UInt64 := 0xFFFFFFFF

def goldilocksP : UInt64 := 0xFFFFFFFF00000001
def goldilocksEps : UInt64 := 0xFFFFFFFF

def codecTagMask : UInt64 := 0xFF
def codecVersionV3 : UInt64 := 3
def sequencerDomainTag : UInt64 := 0x5A

def u64Max : UInt64 := 18446744073709551615

end LeanModel.Constants
