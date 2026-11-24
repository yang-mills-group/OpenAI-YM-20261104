import YM.Integration.WilsonOriginalPublicFigureWickFaces
import YM.Integration.WilsonMaxwellThermometerBareIncidenceRate

/-! Reannounce the finite Wick projection at the engineering scale of each
actual nonzero grade before pricing the common position test. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 460000
namespace YM.Integration.WilsonOriginalPublicFigureWickCharge
open Function Filter Set Finset Lattice Wilson RG Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 XSpace.Retirement Maxwell Maxwell.Wick
open WilsonOriginalPublicFigureWick (project)
open WilsonMaxwellThermometerPositionCurrency (received)
open WilsonMaxwellThermometerBareIncidenceRate (assembled)
open scoped Classical BigOperators Topology
variable {G:Gauge}(W:Initialize G){h d n:ℕ}(F:Labels.Frame G h)

def coin (b:F.Index):Sec G h:=
  (observable G h).rangeRestrict ((W.surveys h).insertW 1 (F.basis b))

theorem deposited (v:F.Coeff):project W F v=∑b:F.Index,v b • coin W F b:=by
  change (observable G h).rangeRestrict ((W.surveys h).insertW 1 (F.coords.symm v))=_
  rw [←F.basis.sum_repr (F.coords.symm v),map_sum,map_sum]
  apply sum_congr rfl
  intro b _
  rw [map_smul,map_smul]
  exact congrArg (· • coin W F b) (congrFun (F.coords.apply_symm_apply v) b)

variable (R:Run G)(g:Fin n→ℕ)(high:∀i,g i≤d)
local notation "L" i:max => R.family.labels.level (g i)
abbrev Address (i:Fin n):= Option (Fin (g i+1) × (L i).Index)

def mark (i:Fin n):Address R g i→Sec G d
  | none=>leaf G d
  | some (k,b)=>up (high i) (en (Nat.le_of_lt_succ k.isLt) (part (g i) k (coin W (L i) b)))

def registered (v:(i:Fin n)→(L i).Coeff)(t:Sample n):Tags G d n:=
  fun i=>up (high i) (received t 1 (project W (L i) (v i)))

def cost (v:(i:Fin n)→(L i).Coeff)(M:Mesh)(s:Finset (Fin n))(i:Fin n):Address R g i→ℂ
  | none=> if i∈s then 0 else 1
  | some (k,b)=> if i∈s then (M.spacing:ℂ)^k.val*v i b else 0

theorem booked (v:(i:Fin n)→(L i).Coeff)(t:Sample n)(s:Finset (Fin n)):
    missing (registered W R g high v t) s=
      assembled d (mark W R g high) (cost R g v t.F s):=by
  funext i
  change (if i∈s then _ else _) = ∑a:Address R g i,cost R g v t.F s i a • mark W R g high i a
  rw [Fintype.sum_option,Fintype.sum_prod_type]
  by_cases hi:i∈s
  · simp only [hi,if_true,cost,mark,zero_smul,zero_add]
    simp only [registered,received,Complex.ofReal_one,one_pow,div_one,deposited,map_sum,map_smul,
      Finset.smul_sum,smul_smul]
  · simp [hi,cost,mark]

theorem wages (v:(i:Fin n)→(L i).Coeff)(M:Mesh)(small:M.spacing≤1)(s:Finset (Fin n))(i:Fin n):
    ∑b:Address R g i,‖cost R g v M s i b‖ ≤ if i∈s then (g i+1:ℕ)*∑b:(L i).Index,‖v i b‖ else 1:=by
  rw [Fintype.sum_option,Fintype.sum_prod_type]
  by_cases hi:i∈s
  · simp only [cost,hi,if_true,norm_zero,zero_add,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg M.positive.le]
    calc
      _ ≤ ∑_k:Fin (g i+1),∑b:(L i).Index,‖v i b‖:=by
        refine sum_le_sum fun k _=>sum_le_sum fun b _=>?_
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ M.positive.le small)
      _ = _ := by simp [nsmul_eq_mul]
  · simp [cost,hi]

theorem original {K:Set (Points n)} (compact:IsCompact K)(apart:K⊆conf n):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀z:pack n,∀o∈M.Box,M.rel z o∈K→
    ∀(v:(i:Fin n)→(L i).Coeff)(s:Finset (Fin n)),
    let t:Sample n:=⟨M,z,o⟩
    let p:=missing (registered W R g high v t) s
    ‖live W d t 0 p-scene (M.rel z o) d p‖≤
      (C*M.spacing)*∏i,if i∈s then (g i+1:ℕ)*∑b:(L i).Index,‖v i b‖ else 1:=by
  obtain ⟨C,pos,fee⟩:=WilsonMaxwellThermometerBareIncidenceRate.moving W d
    (mark W R g high) compact apart
  refine ⟨C,pos,?_⟩
  filter_upwards [fee,frontier.smaller] with M heard small
  intro z o ho hk v s t p
  dsimp only [p]
  rw [booked W R g high v t s]
  apply (heard z o ho hk (cost R g v M s)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg pos M.positive.le)
  exact prod_le_prod (fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _))
    (fun i _=>wages R g v M small s i)

end YM.Integration.WilsonOriginalPublicFigureWickCharge
end
