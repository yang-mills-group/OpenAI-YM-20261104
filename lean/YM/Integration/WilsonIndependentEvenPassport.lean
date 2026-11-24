import YM.WilsonCoeffUV.Auxiliary.Passport
import YM.RegulatorIR.Atlas.Shelves
import YM.Integration.WilsonIndependentGroupedInversionMesh

/-! A single uniform unmarked passport for all two-length plates on one stipulated XSpace.Run. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentEvenPassport
open Lattice RG RG.Supply WilsonCoeffUV WilsonCoeffUV.AuxPlates WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open Precision Source Source.Drops
open scoped Classical BigOperators
variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j:ℕ)

def power (a:ℕ):Side:=⟨V.ratio^a,pow_pos ((by have:=V.large;omega):0<V.ratio) _⟩
def young (a i:ℕ):=i/a
def old (a i:ℕ):=(V.reserve*i*i)/a
def count (a i:ℕ):=old V a i+young a i

structure Menu (extra:ℕ) where
  a : ℕ
  positive : 0<a
  pre : extra≤(power V a).val
  cap : ℝ
  price : Fin a→ℝ
  limits (r:Fin a) : 1≤price r ∧ price r≤cap
  license (r:Fin a) (n c:ℕ)(hc:c≤n) :
    ∃ (A:Levels G)(s:ℕ),A.clock.kernel=K ∧ A.clock.factor j=power V a ∧
      A.clock.factor (j+1)=power V (a+r.val) ∧ Walk A j c s n ∧
      Ally R A chart (extendedY (price r) A.S (s+n)) e s h k

theorem purchased (good:G.Simple)(valid:LocalRatio chart)(branches:∀ p:Patch,p.Branches K G)
    (q:h+3≤j)(late:5≤j)(extra:ℕ) : Nonempty (Menu R chart K V e h k j extra) := by
  obtain ⟨f,ok⟩:=flat_passport good R chart valid K branches e h k j q late
  obtain ⟨a,ha,hf⟩:= WilsonIndependentGroupedInversionMesh.floor V (max f extra)
  have lo : f≤(power V a).val:= (Nat.le_max_left _ _).trans hf
  have z : 0<V.ratio:=by have:=V.large;omega
  have run (r:Fin a) :=ok (power V a) (power V (a+r.val)) lo
    (lo.trans (Nat.pow_le_pow_right z (Nat.le_add_right _ _)))
    V.odd.pow V.odd.pow (Nat.pow_le_pow_right z (Nat.le_add_right _ _))
  choose price shell license using run
  let C:=1+∑ r:Fin a,price r
  have bound (r:Fin a) : price r≤ C:=by
    have H:=Finset.single_le_sum (s:=Finset.univ) (f:=price) (fun t _=>(by linarith [shell t] : 0≤price t)) (Finset.mem_univ r)
    dsimp only [C]
    linarith
  exact ⟨⟨a,ha,(Nat.le_max_right _ _).trans hf,C,price,fun r=>⟨shell r,bound r⟩,license⟩⟩

theorem orbit_floor (G:Gauge)(Y:RegulatorIR.Oracle.Program K)(p d j:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1) :
    let E:=max (RegulatorIR.Atlas.orders G Y p d j γ lo hi) (RegulatorIR.Atlas.orders G Y p d (j+1) γ lo hi)
    ∀ a:ℕ,E ≤ (power V a).val → ∀ r:Fin a,
      RegulatorIR.Atlas.orders G Y p d j γ lo hi ≤ (power V a).val ∧
      RegulatorIR.Atlas.orders G Y p d (j+1) γ lo hi ≤(power V (a+r.val)).val := by
  intro E a he r
  exact ⟨(Nat.le_max_left _ _).trans he,(Nat.le_max_right _ _).trans (he.trans
    (Nat.pow_le_pow_right (by have:=V.large;omega : 0<V.ratio) (Nat.le_add_right _ _)))⟩

variable {extra:ℕ}(M:Menu R chart K V e h k j extra)
theorem plate (i:ℕ) :
    let n:=count V M.a i
    let r:Fin M.a:=⟨i%M.a,Nat.mod_lt _ M.positive⟩
    ∃ (A:Levels G)(s:ℕ),A.clock.kernel=K ∧ Walk A j (n-1) s n ∧
      (∀ m:ℕ,m<n→ A.S.block (s+m)=if m<n-1 then power V M.a else power V (M.a+r.val)) ∧
      (∀ m:ℕ,m≤n→ extendedY (M.price r) A.S (s+n) (s+m)=M.price r) ∧
      Ally R A chart (extendedY (M.price r) A.S (s+n)) e s h k := by
  intro n r
  obtain ⟨A,s,kernel,short,long,walk,all⟩:=M.license r n (n-1) (Nat.sub_le ..)
  refine ⟨A,s,kernel,walk,?_,fun m hm=>y_plate _ _ (Nat.add_le_add_left hm _),all⟩
  intro m hm
  rw [← A.fits.sameFactor, Nat.add_assoc,walk (m+1) hm]
  split_ifs <;> first | exact short | exact long | omega

end YM.Integration.WilsonIndependentEvenPassport
