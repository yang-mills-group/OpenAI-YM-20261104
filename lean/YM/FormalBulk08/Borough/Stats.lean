import YM.FormalBulk08.Borough.Stack
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{M:Bar V}{B:Wait M}{A:Levels G}
variable {U:Empire G K X}{j:ℕ}
structure Poster (K:KernelChoices)(Q:Herald)(F:∀ d,Frame G d)(H:Hol G)(ρ:ChartRatio G)(W:Lab G K X)(j:ℕ):Prop where
    ware: Avenue.Extras W
    glow: Soft (chron W.scrolls) (fun i=>(W.windowD i)⁻¹)
    vac: ∀ E≤j,W.Use ρ E
    bill: ∀ E≤j,Broc.Render W E
    spare: ∀ d D o R E, d+3 ≤ j → d< D → D≤ j → R≤ j→ E≤ j→ Quota (F d) H W o D E R
    marks: ∀ d D o R E l u:_, d+3 ≤ j → d< D → D≤ j → R≤ j→ E≤ j→ u≤ j → l≤ j → VividC u o E D l W Q
lemma stacked (hp:∀ i,Evergreens K Q F H ρ W (U.V i))(k:X→ℕ)(T:X→Time ℕ)(h:5≤j)(hr:∀ x,j≤ (U.V x).clock.J (k x+1))(hb: Years (register G K U W k T).scrolls) (hw:Soft (chron (register G K U W k T).scrolls) (fun i=>ageZ ((U.V i.a).clock.hatBeta i.b))) : Poster K Q F H ρ (register G K U W k T) j:= by
    obtain ⟨a,b,P⟩:= can_bill hp T k hb hw j h hr; exact ⟨a,b,fun E he=> (P E he).1,fun E he=>(P E he).2.1,fun _ _ o _ _ hu hv hx hy hz=> ((P _ hz).2.2 _ _ hu hv hx o _ hy).1,fun d D o R E _ _ hd hD ht hR hE hl hm=> ((P _ hE).2.2 _ _ hd hD ht o _ hR).2 _ hm _ hl⟩
lemma presold (hG:G.Simple)(hp:∀ i,Evergreens K Q F H ρ W (U.V i))(k:X→ℕ)(h:5≤j)(hr:∀ x,j≤ (U.V x).clock.J (k x+1)) : Poster K Q F H ρ (register G K U W k (fun i=>lyre (U.V i))) j := by
    refine stacked hp k _ h hr (supply_lyre hG hp k) ((soft_day _).below ?_);intro i;change _≤|(lyre _).day _|; rw [measure (hp i.a)]
-- incl all ages. Captured k may be outside tail if using generic operations.
lemma log_day (hG:G.Simple)(hp:∀ i,Evergreens K Q F H ρ W (U.V i))(k y:X→ℕ)(u:X→ℝ)(hu:∀ i,0≤u i)(he:∀ i,ageZ ((U.V i).clock.hatBeta (y i)) ≤ 2+u i) :
    let R:=(register G K U W k (fun i=>logtime (U.V i).S (y i) (u i) (hu i))); Soft (chron R.scrolls) (fun i=>ageZ ((U.V i.a).clock.hatBeta i.b)) := by
   intro P; refine ⟨1+G.slopeConstant,1,add_nonneg zero_le_one (Gauge.slopeConstant_pos hG).le,fun x=>?_⟩; let S:= U.V x.a; let z:=ageZ ∘ S.clock.hatBeta; let b:=y x.a; let u':=u x.a
   change |z x.b| ≤ _; rw [abs_of_nonneg (show 0≤ z x.b from zero_le_one.trans (progZ ((hp x.a).beta x.b))),pow_one]; have ht:=mul_le_mul_of_nonneg_right (show 1 ≤ 1+G.slopeConstant from le_add_of_nonneg_right (Gauge.slopeConstant_pos hG).le) ((chron _).good x)
   by_cases hh:x.b≤ b
   · rw [one_mul] at ht; exact ((ages _ S hG (hp x.a).beta hh).2.1.trans (he x.a)).trans ((le_add_of_nonneg_right (abs_nonneg (S.S.scale x.b - S.S.scale b))).trans ht)
   have hh':= le_of_not_ge hh; obtain hg:= (ages _ S hG (hp x.a).beta hh').2.2; let c:= sowing S.S b x.b; change _ ≤ _*(2+u'+|c|); have hw:c≥0:=sowing_plus _ hh'; rw [abs_of_nonneg hw];refine hg.trans ?_; change z b+G.slopeConstant*c ≤ _; have hX:z b≤2+u' := he x.a; have hU:0≤u':=hu x.a; nlinarith only [hX,hU,hw,Gauge.slopeConstant_pos hG]
lemma dated (hG:G.Simple)(hp:∀ i,Evergreens K Q F H ρ W (U.V i))(k y:X→ℕ)(u:X→ℝ)(hu:∀ i,0≤u i)(he:∀ i,ageZ ((U.V i).clock.hatBeta (y i)) ≤ 2+u i)(h:5≤j)(hr:∀ x,j≤ (U.V x).clock.J (k x+1)) : Poster K Q F H ρ (register G K U W k (fun i=>logtime (U.V i).S (y i) (u i) (hu i))) j:= by
   have hs:= log_day hG hp k y u hu he; refine stacked hp _ _ h hr ?_ hs; refine dawn _ y u hu (fun x=>rfl) (hs.below ?_); intro i; obtain ⟨B,b,H,S⟩:=(hp i.a).payment i.b; simp only [Nat.abs_cast]; exact S.1.trans (H.trans (le_abs_self _))
-- convenience `Z=1+Λ_k`
def Lambda (A:Levels G) (i:ℕ):= 2+Real.log (A.clock.hatBeta i)
lemma spend (hp:Evergreens K Q F H ρ W A)(y):0 ≤1+ Lambda A y ∧ ageZ (A.clock.hatBeta y) ≤ 2+(1+Lambda A y):= by
   let x:=A.clock.hatBeta y; have hx:=hp.beta y; have hu:= (Real.exp_pos _).trans_le hx; have he:= (Real.le_log_iff_exp_le hu).2 hx; let b:=Real.log x; change 1 ≤ b at he; change 0≤1+(2+b) ∧ 1+Real.log b≤2+(1+(2+b)); have hp:= Real.log_le_sub_one_of_pos (zero_lt_one.trans_le he); constructor <;> linarith
lemma current_admits (U:Empire G K X)(j:ℕ): ∃ k:X→ℕ,∀ q,k≤q→∀ x,j≤ (U.V x).clock.J (q x+1) := by
   choose K H using fun x:X=> eventually_atTop.mp ((U.V x).fits.deep.eventually (eventually_ge_atTop j))
   exact ⟨K,fun q h x=> H _ _ (Nat.le_add_right (q x) _|>le_trans (h _))⟩
end YM.FormalBulk08.Borough
