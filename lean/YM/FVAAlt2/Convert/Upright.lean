import YM.FVAAlt2.Convert.Uplift
/-! non-leading bending coefficients of `Launch`: for physical PS near-position branch.
 Proves upright on all specified cutoffs, not a leading positive parameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position
open FormalOPE.RG10.Position (Plan)
open FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon MS MS.Koszul MS.Local.Physical MS.Menus MS.Book MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Report Matrix Profiles
open scoped BigOperators Topology PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F:Frames G}{B:MS.Local.Physical.Deck G}{X:Prescription B} {V:Booked B} {Z:RichBook B} {T:MS_Data G V}
variable {d k n m:ℕ}(μ:ℝ)
local notation "J"=> RG10.Position.Deck F d
local notation "H"=> mast B d F
local notation "K"=> din F B d
local notation "R"=> dout F B d
local notation "L"=> Glyph B d
local notation "A"=> stepR F B d
set_option linter.unusedSectionVars false
section cros
variable (F B)(d)
lemma scenery (s:Signed): Position.Grade.swing (F:=F) d s*R= R*A s:= by
   let v:=RG10.Position.deck F d; let X:=RG10.Position.Grade.swing (F:=F) d s; let D:= ride F (Signed.inclusionO s) d; have hr(i:J): D (v i)=∑ j:J,(X i j:ℂ) • v j:= by simp_rw [X,Position.Grade.swing_deck]; exact (v.sum_repr _).symm
   ext i j : 1; apply Complex.ofReal_injective; rw [Matrix.mul_apply,Matrix.mul_apply]; push_cast
   let W:=D ( v i ); let uAt (x:L): ℂ:= (H).repr W x; apply Eq.trans (b:=uAt j) ?_ ?_; rotate_left
   all_goals unfold uAt W
   · rw [← tally_b F B i,map_sum,map_sum]; simp_rw [ Finsupp.finsetSum_apply,map_smul, Finsupp.smul_apply,dout_at,movesOn ]; rfl
   rw [hr i,map_sum,Finsupp.finsetSum_apply]; simp_rw [map_smul,Finsupp.smul_apply,dout_at]; rfl
lemma theatre (s:Signed): K*Position.Grade.swing (F:=F) d s= A s*K:=by
   let S:= Position.Grade.swing (F:=F) d s;
   calc _= ( K*S )*( R*K ) := by rw [dout_mul,Matrix.mul_one]
        _= _:= by rw [Matrix.mul_assoc,← Matrix.mul_assoc S, scenery F B,← Matrix.mul_assoc,←Matrix.mul_assoc,din_mul,Matrix.one_mul]
lemma higher0 : ∀ (u:J)(x:L), Position.Deck.price F d u≠x.size→ R u x=0 ∧ K x u=0:=by
 intro u x h; have he:Position.Deck.grades F d u≠(x.size,x.grade):=fun e=> h (congr_arg Prod.fst e); constructor<;> (apply Complex.ofReal_eq_zero.mp); · rw [dout_at,cite_b F B x u he]
 rw [din_at,cite_c F B x u he]
end cros
lemma owner_zero (h:Launch Z T (F:=F) X)(n:ℕ)(hp:0<n)(a x:ℝ)(i j:L)(hi:i.size=0): coeff n (beamA X x a d i j)=0:=by
 obtain ⟨⟨u,hu⟩,x'⟩:=i; change u=0 at hi; subst u; let i:L:=⟨ ⟨0,hu⟩,x' ⟩
 by_cases hx:j∈ Set.range (up (high i) (B:=B)); · obtain ⟨k,rfl⟩:=hx; rw [beam_cost,show ((X.fees (Lobby.owner ⟨⟨0,hu⟩, x'⟩).h (Lobby.owner ⟨⟨0,hu⟩,x'⟩).item n).register k)=_ from h.unit x' n hp k,Polynomial.eval_zero,mul_zero]
 rw [beam_no X x a _ _ hx,map_zero]
variable (q:ℕ+)
local notation "Ω"=> frameO F B q m μ X d
local notation "σ"=> beamA X (μ-Θ q m) (epsilon q m) d
local notation "W"=> ℝ
lemma tbeam : Stg ( Ω ) n= R * ((σ).map (coeff n) * K):= by
   ext i j : 1; simp_rw [Stg,frameO, Matrix.of_apply, Matrix.mul_apply,Matrix.map_apply,map_sum, PowerSeries.coeff_C_mul, map_sum,PowerSeries.coeff_mul_C ]
variable (Ωx: Launch Z T (F:=F) X)(hn:0<n)
include Ωx hn
lemma thigher : Stg (frameO F B q m μ X d) n∈ tents F d:= by
   apply pinned _ |>.mpr;
   rw [votes,tbeam]; constructor;
   · constructor
     · intro i j e; rw [ show ( Matrix.of (R* ((σ).map (coeff n) * K)) )=R* ((σ).map (coeff n)*K) from rfl,Matrix.mul_apply ]; apply Finset.sum_eq_zero; intro k _; by_cases he: Position.Deck.price F d i=k.size; swap; · rw [ (higher0 F B d _ k he).1, zero_mul ]
       rw [Matrix.mul_apply,Finset.sum_eq_zero,mul_zero]; intro u _; by_cases hf : Position.Deck.price F d j = u.size; · rw [Matrix.map_apply, lonely X _ _ _ _ ( by rw [ ←he, ←hf ]; exact e ),map_zero,zero_mul]
       rw [ (higher0 F B d _ u hf).2, mul_zero ]
     intro s; let M:=(σ).map (coeff n); let T:= Position.Grade.swing (F:=F) d s
     change R * (M*K)*T=T*( R* (M*K)); rw [Matrix.mul_assoc, Matrix.mul_assoc M, theatre F B d s,← Matrix.mul_assoc T, scenery, Matrix.mul_assoc, ← Matrix.mul_assoc (A s), ← Matrix.mul_assoc M]; rw [show A s*M=M* A s from Matrix.ext fun i j=> cut_cos F X s _ _ Ωx.rent i j]; -- args order inspect
   funext j; rw [ Matrix.mul_apply ]; apply Finset.sum_eq_zero; intro k _; by_cases ht : k.size = 0; · let i:J:=Position.Deck.start F d; rw [ Matrix.mul_apply,Finset.sum_eq_zero,mul_zero]; intro u _; rw [ Matrix.map_apply,owner_zero Ωx n hn _ _ _ _ ht,zero_mul]
   rw [( higher0 F B d _ k (fun h=> ht (h.symm.trans rfl)) ).1,zero_mul]
omit Ωx hn
-- exact seats used with top physical branch.
variable (P:Plan F)(D:ChartRatio G)(g:G.Simple)(hD: LocalRatio D){T':Booked (seats P.liftOff P.certified)}{X':Prescription (seats P.liftOff P.certified)}{U': MS_Data G T'}
local notation "E"=> seats P.liftOff P.certified
variable (Hᵤ: Launch ( F:=F ) (Lobby.Table ( nativeR P ) ( seats P.liftOff P.certified )) U' X')
include Hᵤ g D hD
lemma tired : UprightMS P X' μ:= by
   intro q m d; let V:= (fares P X' μ q m d); let S:= seats P.liftOff P.certified; apply Upright.obtainable V; · rw [show Stg V 0=(frameO F S q m μ X' d).map (constantCoeff : PowerSeries ℝ →+* ℝ) from Matrix.ext fun _ _=> PowerSeries.coeff_zero_eq_constantCoeff_apply _,Report.map_element, Report.clearly P D U' 2 μ X' hD (by decide) g Hᵤ.high d,Matrix.one_mul,dout_mul,sub_self]; exact Submodule.zero_mem _
   intro n hn; exact thigher μ q Hᵤ hn
end YM.FVAAlt2.Convert
