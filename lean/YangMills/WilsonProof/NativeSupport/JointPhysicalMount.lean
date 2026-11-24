import YangMills.WilsonProof.NativeSupport.JointPlantedOld
import YangMills.WilsonProof.NativeSupport.JointProjectionLedger
import YangMills.WilsonProof.NativeSupport.JointPhysicalHeap
import YangMills.WilsonProof.NativeSupport.JointCashAdmission

/-! Mount the full inherited proper packet and the actual primitive
sources on a single reserved ticket. The same hats are used for the
native marked purchase and the old full-exponent physical price. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker MeasureTheory MergeProof MergeProof.Accent MergeProof.Menu
open Extra.Multi Extra.Trajectories Progress.DirectedRecipe Planned.GuardedAtom RGGapR2 Push.GridApprox.Nil Packet Painted
open scoped Classical BigOperators
variable {V J:Type} [Fintype V] [DecidableEq V] [Fintype J] {G:Gauge} {n:Side} (R:Rep G n)
local notation "B" => Stock.census V
local notation "C" => Stock.census (Ink V)
local notation "M" => (Stock.census (Ink V)).Mode
variable (o:V → Site n) (w:V → ℝ) (H:Support n → Config G n → Marker.Poly (Stock.census V))
variable (K:Box n → Config G n → Marker.Poly (Stock.census V))
variable (born:Finset V) (birth:J → V) (X:J → Support n) (v:J → Config G n → ℂ) (amp:J → ℝ)
variable {A D U a quiet t offer:ℝ} {μ:ℕ}
local notation "a₀" => (fun j:J=>newborn (birth j))
local notation "wv" => Painted.weight w A D born
local notation "E" => plantedLog R C (liftSheet H) a₀ X v
local notation "L" => plantedDirty R C (liftSheet K) a₀ X v
local notation "ou" => A*((μ:ℝ)*siteFactor R.p.B*U)
local notation "nu" => (μ:ℝ)*siteFactor R.p.B*(D*t)

theorem physical_mount (slots:HasSlots R.p R.activities) (vac:R.activities.Valid R.p a quiet)
    (prev:Rough.Ledger o H K R.p.threshold) (re:RootedSheet R.p id H w U) (rk:RootedSheet R.p Prod.fst K w U)
    (oldH:∀ i s,Vivid H i (tag s) → Disjoint s born) (oldK:∀ i s,Vivid K i (tag s) → Disjoint s born)
    (u0:0 ≤ U) (aa:1 ≤ A) (ad:1 ≤ D) (hw:∀ i,0 < w i) (cert:∀ j,birth j∈born) (distinct:Injective birth)
    (home:∀ j,o (birth j)∈X j) (loc:∀ j,LocalOn (X j) (v j)) (sym:∀ j,GaugeInvariant (v j)) (meas:∀ j,Measurable (v j))
    (apos:∀ j,0 ≤ amp j) (bound:∀ j Z,‖v j Z‖ ≤ amp j)
    (occ:Occupancy o μ) (occ':Occupancy (o ∘ (Prod.fst : Ink V → V)) μ)
    (t0:0 ≤ t) (stencil:∀ j,Real.exp (R.p.supportExponent*coverNumber R.p.B (X j))*(w (birth j)*amp j) ≤ t)
    (exp0:0 ≤ R.p.supportExponent-4)
    (room:((R.p.B+R.p.B+1:ℕ):ℝ)^4*(quiet+ou+nu) ≤ 3)
    (ceiling:fullFare (mountedFare quiet ou nu) ≤ offer) :
    ∃ q:(VividId E ⊕ VividId L) → Hat (Stock.census (Ink V)) R,
      Offer (o ∘ Prod.fst) (heap q) wv R.p.B (R.p.supportExponent-4) offer ∧
      (∀ j (Z:Rep G n),HasSlots Z.p Z.activities → (heap q j).M.turn.blank Z) ∧
      (∀ i,∃ u∈(q i).s.val,u∈active born) ∧
      (∀ y:V,(∑ i:VividId E ⊕ VividId L with y∈(q i).s.val.image Prod.fst ∧ ¬gains born (q i).s.val,
        sumFee (q i) (fun u:Ink V=>w u.1)*MergeProof.load (q i).M) ≤ 4*U) ∧
      (∀ Z,∑ i,odour (q i) Z=∑ i,E i Z) ∧ (∀ i Z,∑ j,fragrance (q j) Z i=L i Z) ∧
      ∀ Z,play R C (exclaim R.activities C+L) (fun U'=>∑ i,E i U') Z=
        play R C (exclaim R.activities C+liftSheet K) (fun U'=>∑ i,liftSheet H i U') Z*
          ∏ j,(1+Poly.send ((Stock.census (Ink V)).fire (a₀ j)) (v j Z)) := by
  obtain ⟨eh,eh0,ehv,ehr⟩:=re
  obtain ⟨ck,ck0,ckv,ckr⟩:=rk
  have az:=zero_lt_one.trans_le aa
  have dz:=zero_lt_one.trans_le ad
  have wp (i:Ink V):0 < wv i := by have h:=hw i.1;unfold Painted.weight;split <;> split <;> positivity
  let e:=R.p.supportExponent-1
  have plus:e+1=R.p.supportExponent := by dsimp only [e];ring
  have he:=rooted_input R.p.B μ e U R.p.threshold A D u0 az.le w hw born o occ id H
    (fun i=>(prev.exp i).toBorne) (fun i Z=>(prev.exp i).sil Z) oldH eh eh0 ehv (by rwa [plus])
  have hk:=rooted_input R.p.B μ e U R.p.threshold A D u0 az.le w hw born o occ Prod.fst K
    (fun i=>(prev.flag i).1.toBorne) (fun i Z=>(prev.flag i).2 Z) oldK ck ck0 ckv (by rwa [plus])
  have inc:Injective a₀ := fun i j eq=>distinct (congrArg Prod.fst eq)
  have freshBorn b j:=fresh_borne R C a₀ X v (o ∘ Prod.fst) home loc sym meas b j
  have freshPay b:=fresh_towed R C a₀ X v (o ∘ Prod.fst) home inc wv wp amp apos bound occ' e (D*t) (mul_nonneg dz.le t0)
    (fun j=>by
      rw [plus,new_weight w A D born _ (cert j)]
      calc
        _ = D*(Real.exp (R.p.supportExponent*coverNumber R.p.B (X j))*(w (birth j)*amp j)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (stencil j) dz.le) b
  have law:=plant_ledger R C (o ∘ Prod.fst) (liftSheet H) (liftSheet K) a₀ X v vac (lift_ledger R o H K prev)
    wv wp he hk freshBorn freshPay exp0 room
  obtain ⟨proper,priceE,priceK,_,exactDensity⟩:=law
  have old (p:M) (nq:p ≠ (Stock.census (Ink V)).quiet) (none:Disjoint (p.val.image Prod.fst) born) :=
    planted_old_parts R o H K birth X v born cert prev vac p nq none
  have rawE := old_envelope (born:=born) H E eh ehv (fun i Z=>(proper.exp i).sil Z) eh0 (fun p ne no=>(old p ne no).1)
  have rawK := old_envelope (born:=born) K L ck ckv (fun i Z=>(proper.flag i).2 Z) ck0 (fun p ne no=>(old p ne no).2)
  let frugal:=univ.filter (fun p:M=>¬gains born p.val)
  obtain ⟨q,mounted,blank,regular,dirt,modeE,modeK,prices⟩:=dock_caps slots proper priceE priceK wp frugal
    (fun i=>oldCap (eh i)) (fun i=>oldCap (ck i))
    (fun i Z p hit=>rawE.1 i Z p (mem_filter.mp hit).2) (fun i Z p hit=>rawK.1 i Z p (mem_filter.mp hit).2)
  refine ⟨q,?_,heap_reserved q blank,?_,?_,regular,dirt,exactDensity⟩
  · exact Offer.fatten (Menu.counts (q:=q) (v:=wv) (h:=wp) (hp:=mounted) (hd:=exp0)) ceiling
  · intro i
    rcases i with i|i
    · rw [modeE];exact rawE.2 i.1 i.2.1.val i.2.1.property
    · rw [modeK];exact rawK.2 i.1 i.2.1.val i.2.1.property
  · let base (u:Ink V):=w u.1
    obtain ⟨er,kr⟩:=prices base (fun z=>hw z.1)
    intro y
    have echarges:=mounted_old_bill id E (fun i=>q (.inl i)) modeE eh eh0 w hw born
      (fun i p hp=>er i p (mem_filter.mpr ⟨mem_univ _,hp⟩)) y
    have kcharges:=mounted_old_bill Prod.fst L (fun i=>q (.inr i)) modeK ck ck0 w hw born
      (fun i p hp=>kr i p (mem_filter.mpr ⟨mem_univ _,hp⟩)) y
    simp only [sum_filter,Fintype.sum_sum_type,id_eq] at echarges kcharges ⊢
    have eroot:=ehr y
    have kroot:=ckr y
    simp only [sum_filter,id_eq] at eroot kroot
    apply (add_le_add echarges kcharges).trans
    linarith only [eroot,kroot]

end YM.Integration.InletSusceptibility.JointShadow
