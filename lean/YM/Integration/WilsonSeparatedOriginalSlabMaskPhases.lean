import YM.Integration.WilsonReportHarvestSlabCubic

/-! Every mask is an average of eight unit shifts of the original occupied reading. Its absolute coefficient sum is one. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonSeparatedOriginalSlabMaskPhases
open Finset RG Push Local MergeProof Marker Accent Extra.Trajectories RG05Readout RG05Readout.Many
open WilsonReportHarvestSlabLabels WilsonReportHarvestSlabShiftLabels
open scoped BigOperators
local notation "S₀"=>Stock.census (Fin 3)
open private formula bucket from YM.Integration.WilsonReportHarvestSlabCubic

def mark (b:Fin 8)(i:Fin 3):ℤ:=if b.val.testBit i.val then -1 else 1

def character (b:Fin 8)(s:Finset (Fin 3)):ℤ:=∏i∈s,mark b i

private theorem exactTable:∀s t:Finset (Fin 3), (∑b:Fin 8,character b s*character b t)=(if s=t then 8 else 0):=by decide

def shift (b:Fin 8)(i:Fin 3):ℂ:=(mark b i:ℂ)

def weight (q:(S₀).Mode)(b:Fin 8):ℂ:=(character b (univ\q.val):ℂ)/8

theorem unit (b:Fin 8)(i:Fin 3):‖shift b i‖≤1:=by unfold shift mark;split<;>norm_num

theorem price (q:(S₀).Mode):∑b:Fin 8,‖weight q b‖=1:=by
  have pm (b:Fin 8)(i:Fin 3):‖(mark b i:ℂ)‖=1:=by unfold mark;split<;>norm_num
  have size (b:Fin 8)(t:Finset (Fin 3)):‖(character b t:ℂ)‖=1:=by
    unfold character;rw [Int.cast_prod,norm_prod];simp only [pm,Finset.prod_const_one]
  have each (b:Fin 8):‖weight q b‖=(1:ℝ)/8:=by unfold weight;rw [norm_div,size];norm_num
  simp only [each];norm_num

private theorem realTable (s t:Finset (Fin 3)):
    (∑b:Fin 8,(character b s:ℂ)*(character b t:ℂ))=(if s=t then 8 else 0):=by
  have h:=exactTable s t
  by_cases eq:s=t
  · rw [if_pos eq] at h ⊢;exact_mod_cast h
  · rw [if_neg eq] at h ⊢;exact_mod_cast h

theorem original (A:Poly S₀)(q:(S₀).Mode):
    (∑b:Fin 8,weight q b*(translated (shift b) A).part entire)=A.part q:=by
  classical
  let c:Finset (Fin 3):=univ\q.val
  have sum (t:Finset (Fin 3)) : (∑b:Fin 8,weight q b*(A.part (bucket (univ\t))*∏i∈t,shift b i))=
      (if c=t then A.part (bucket (univ\t)) else 0):=by
    change (∑b:Fin 8,(character b c:ℂ)/8*(A.part (bucket (univ\t))*∏i∈t,(mark b i:ℂ)))=_
    have code(b:Fin 8): (∏i∈t,(mark b i:ℂ))=(character b t:ℂ):=by simp [character]
    simp_rw [code]
    calc
      _=A.part (bucket (univ\t))/8*(∑b:Fin 8,(character b c:ℂ)*(character b t:ℂ)):=by
        rw [Finset.mul_sum];apply sum_congr rfl;intro b _;ring
      _=_:=by rw [realTable];split<;>simp
  simp_rw [formula,Finset.mul_sum]
  rw [Finset.sum_comm];simp_rw [sum]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl];congr 1;apply Subtype.ext;ext i;simp [bucket,c]
  · intro i _ hi;exact if_neg hi.symm
  · intro hc;exact (hc (Finset.mem_powerset.2 (Finset.subset_univ _))).elim

end YM.Integration.WilsonSeparatedOriginalSlabMaskPhases
