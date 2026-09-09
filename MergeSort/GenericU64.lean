import MergeSort.Generic
/-! The `UInt64`-`≤` instantiation of the generic merge loop, in its own module so that the C
    compiler keeps it as a separate function (the generic code specialised here, nothing else). -/
namespace MergeSort.G
open UInt64Array

/-- Specialised kernel: `mergeLoop` with the comparison fixed. -/
def kernelU64 : Kernel := fun lo mid hi src dst hsz hs hd hlo hmid =>
  mergeLoop (fun a b => decide (a ≤ b)) mid hi lo mid lo src dst hsz hs hd hmid (by omega) (by omega) (by omega)

end MergeSort.G
