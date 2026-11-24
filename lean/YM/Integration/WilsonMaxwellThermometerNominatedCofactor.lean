import YM.Integration.WilsonMaxwellThermometerNominatedColumns

/-! The finite lower contrast is applied to all four proper and full faces
which read the actual cubic at the origin, with the same two displaced inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedCofactor
open Filter Lattice Wilson Labels RG Source MeasureTheory PhysicalNext.Repeat.Legato
open WilsonPositionThermometerCapStation WilsonNeutralOffsetCutoff
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (N p:ℕ)
local notation "U" => Config G (R.family.side N p)
local notation "S₀" => Site (R.family.side N p)
local notation "slots" => Finset (Fin 3)
local notation "origin" => WilsonThermometerAlignedCells.atOrigin
local notation "Ω" => R.family.omega N p

def file {d:ℕ} (x:R.family.label d) (z:S₀):C(U,ℂ):=
  ⟨R.family.O N p x z,R.family.continuousO N p d x z⟩

def native (o:S₀×S₀) (i:Fin 3):C(U,ℂ):=file R N p (named R A N p i) (origin o i)

def mean : C(U,ℂ)→ₗ[ℂ]ℂ where
  toFun X:=Ω X
  map_add' X Y:= by
    unfold Family.omega moment
    exact integral_add (continuous_integrable _ X.continuous) (continuous_integrable _ Y.continuous)
  map_smul' c X:=by
    unfold Family.omega moment
    exact integral_const_mul c X

def companions (o:S₀×S₀) (s:slots):C(U,ℂ):=
  ∏j∈s.erase 0,native R A N p o j

def marked (o:S₀×S₀) (s:slots):C(U,ℂ)→ₗ[ℂ]ℂ where
  toFun X:=mean R N p (X*companions R A N p o s)
  map_add' X Y:=by rw [add_mul,map_add]
  map_smul' c X:=by rw [smul_mul_assoc,map_smul];rfl

def held (o:S₀×S₀) (s:slots):ℂ:= mean R N p (companions R A N p o s)

def table (o:S₀×S₀) (X:C(U,ℂ)) (s:slots):ℂ:=
  if (0:Fin 3)∈s then marked R A N p o s X else held R A N p o s

def reading (o:S₀×S₀):C(U,ℂ)→ₗ[ℂ]ℂ:=
  marked R A N p o Finset.univ -
    ((held R A N p o {2}) • marked R A N p o {0,1} +
     (held R A N p o {1}) • marked R A N p o {0,2} +
     (held R A N p o {1,2}) • marked R A N p o {0}) +
    (2*held R A N p o {1}*held R A N p o {2}) • marked R A N p o {0}

theorem connected (o:S₀×S₀) (X:C(U,ℂ)) :
    WilsonPositionThermometerConnected.value (table R A N p o X)=reading R A N p o X := by
  simp [WilsonPositionThermometerConnected.value,table,reading]
  ring

theorem filed (o:S₀×S₀) (s:slots) :
    table R A N p o (native R A N p o 0) s=
      Ω (fun W=>∏i∈s,R.family.O N p (named R A N p i) (origin o i) W) := by
  let f:=native R A N p o
  have work (v:C(U,ℂ)) (word:v=∏i∈s,f i):
      mean R N p v=Ω (fun W=>∏i∈s,R.family.O N p (named R A N p i) (origin o i) W) := by
    rw [word]
    change Ω (⇑(∏i∈s,f i))=_
    congr 1
    funext W
    change (∏i∈s,f i) W=∏i∈s,f i W
    clear word v
    induction s using Finset.induction_on with
    | empty=>rfl
    | insert j s hj ih=>
      rw [Finset.prod_insert hj,Finset.prod_insert hj]
      exact congrArg (f j W * ·) ih
  by_cases present:(0:Fin 3)∈s
  · rw [table,if_pos present]
    exact work _ (Finset.mul_prod_erase s f present)
  · rw [table,if_neg present]
    apply work
    unfold companions
    rw [Finset.erase_eq_of_notMem present]

theorem original (o:S₀×S₀) :
    reading R A N p o (native R A N p o 0)=
      WilsonPositionThermometerConnected.value (fun s=>Ω (fun W=>∏i∈s,
        R.family.O N p (named R A N p i) (origin o i) W)) := by
  rw [←connected,funext (filed R A N p o)]

end YM.Integration.WilsonMaxwellThermometerNominatedCofactor
