import YM.FVA2.XReg.Coupling
/-!
# Exact position identity for the regulator frames

Both frames in the near-free `Executed` setting. This uses formal-series
substitution of the reset coupling q into the position reports Z
(initial, before D), not comparing truncations. If D is also `Formal`
and identity in order zero (shown in `Dframe/Bare`), the positioned
`deck` on the posted arrays, right-composed onto D, MUST equal the
reexpression of the original position solve. No hypothesis about
convergence/boundedness of D. See `XReg/Post` for eventuality along
the regulator schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Unique
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point
open scoped Topology ContDiff BigOperators Classical Matrix
variable {n d k:ℕ}{G:Gauge}{B:Deck G}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
-- reality via PowerSeries emit
abbrev CoreR (q:Cn): Prop:= PowerSeries.map (starRingEnd ℂ) q=q
variable {q:Cn}(h:Rooted q)(s:CoreR q)
lemma of_star (h:∀ i:ℕ, star (coeff i q)=coeff i q): CoreR q:= PowerSeries.ext fun i=> by rw [coeff_map]; exact h i
include s
lemma coinR (i:ℕ) : star (coeff i q)=coeff i q:= by change starRingEnd ℂ _=_; rw [← coeff_map,s]
lemma charge_p (i j:ℕ): (↑(( Program.cut q i j ).re):ℂ)= Program.cut q i j:= by
    unfold Program.cut; obtain hc : star ( coeff j (q^i) )=_:= coinR (q:=q^i) (show PowerSeries.map (starRingEnd ℂ) (q^i)=q^i from by rw [map_pow,s]) j; exact Complex.conj_eq_iff_real.mp hc |>.elim (fun x hx=> (by rw [hx]; rfl)) -- orientation exists?
lemma prices {E:Type}[AddCommGroup E][Module ℂ E][Module ℝ E][IsScalarTower ℝ ℂ E] (i j:ℕ)(p:E): ( Program.cut q i j ) • p=( Program.cut q i j ).re • p:= by
    nth_rw 1 [ ← charge_p s i j ]; exact IsScalarTower.algebraMap_smul ℂ ( Program.cut q i j ).re p -- no _ actions
variable (z: Pick G d)(Z:Reports G d)
variable (D: Guard G d){A:Screen G d} (R:Fray A)(hs: A.Prepared)
-- coupling on deck including real.R
abbrev shift (z:Pick G d)(q:Cn) : Pick G d:= fun i=>∑ j∈Finset.Iic i, (Program.cut q j i).re • z j
omit s in
lemma shift_top : shift z q 0=z 0:= by rw [shift, show Finset.Iic (0:ℕ)={0} from Finset.ext (by simp) ]; simp [Program.cut]
lemma fees : stepV q (deck z)= deck (shift z q):= by
    refine PowerSeries.ext fun i=>?_; by_cases hp:i=0; · subst i; rw [stepV,coeff_mk,pay0,decked,decked,pulling,pulling, shift_top ]; -- verify
    rw [ stepV, coeff_mk, pos_decked ( shift z q ) hp, rules ]; unfold shift; rw [AddSubmonoidClass.coe_finsetSum]; refine Finset.sum_congr rfl (fun j _=>?_ ); by_cases hv:j=0; · subst j; rw [ Program.cut,pow_zero,coeff_one,if_neg hp,Complex.zero_re,zero_smul,zero_smul ]; rfl
    rw [ pos_decked z hv, prices s]; rfl
-- NOTE doesn't require const unit T for moving solve. See `duplicate` for use with the `Executed` hypotheses. No finiteness hidden.
include h
lemma euclidean (hu: A.Solved z Z): A.Solved ( shift z q ) ( substitute q Z ):= by
 intro l; rw [← fees s, resetR q _ Z h ]; by_cases hp:l=0; · subst l; rw [pay0]; exact hu 0
 rw [if_neg hp,rules]; simp_rw [prices s,map_sum, _root_.map_smul ]; refine Finset.sum_eq_zero (fun i _=>?_ ); rw [hu i]; split_ifs with he; · subst i; simp [Program.cut,hp]
 exact smul_zero _

omit s h
lemma inject (u v:Normalize.Change G d)(h0:stand u=stand v): u=v:= by apply Subtype.ext; ext1 p; exact add_left_cancel (DFunLike.congr_fun h0 p: p+ u.val p=p+ v.val p)
lemma eon (t:Cn)(D: Guard G d) (hD:constantCoeff D=1): realm D (substitute t Z) 0= Z 0:= by rw [Normalize.rest,coeff_zero_eq_constantCoeff_apply,hD, pay0]; rfl
local notation "P"=> realm D (substitute q Z)
include h s
theorem duplicate (hA:Fray.Executed R hs Z) (hp:Formal D)
        (hD:constantCoeff D=1) (he:Executed R hs (realm D (substitute q Z))) :
        D * deck (Lays R hs (realm D (substitute q Z))) = stepV q (deck (Lays R hs Z)):= by
    let u:= Lays R hs Z
    let x:= shift u q
    let v:= Lays R hs P
    obtain ⟨t,ht⟩:= ( hp.product he.1 ).actions
    -- leading agreement using D identity at this regulator
    have hi: u 0=v 0:= by unfold u v; rw [leads,leads,eon Z q D hD]
    have hu: t 0=u 0:= by apply inject; rw [hi,← const_deck, ← const_deck, ← ht, map_mul,hD,one_mul]
    have hk : t 0=x 0:= hu.trans (shift_top u).symm
    -- after composing t must then be *the* solution
    have hT: realm (deck t) (substitute q Z)= realm (deck v) P := by
      unfold v; rw [ ← ht, ← parlance ]
    have hA': Injective ( slope A (x 0) ((substitute q Z) 0) ):= by
      rw [ ← hk, hu, pay0 ]; exact hA.2.2.1
    have H: x=t:= Screen.shift_unique A (substitute q Z) x t hk.symm
      ( euclidean h s u Z hA.2.1 ) (fun i=> by rw [hT]; exact he.2.1 i) hA'
    rw [ ht, ← H, fees s]
end YM.FVA2.Reg.Unique
