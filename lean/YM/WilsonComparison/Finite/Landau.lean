import YM.WilsonComparison.Finite.Sources

/-!
# All-order Landau and MS-Puff diagram identity

Top sign convention: bosonic fiscal contribution to action nonnegative; vertex is MINUS that
plus log(ratio). Here work PRIOR to any bulk coupling re-expression;
`NRG` after unscaling will be connected by change of independent formal variable.
This file is at native `a=1`. `logAlphabet` is a site-torus expression, all
finite stencils, and includes the correct orbit half. No other normalization or
counterterm implicit. The denominator is the common zero-source vacuum series
(this is terminal/top PT, *not* the open-field step).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Precision Lattice
open MS MS.Landau MS.Swirl MS.Swirl.Near MS.Orbit MS.Orbit.Cog MS.Native MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP
open MSBar MSBar.Cutis MSBar.Cutis.Winter MSBar.Loft MSBar.Bric MSBar.Inlay MSBar.Odom
open Bric.Coil Barr
open PowerSeries (coeff)
open scoped BigOperators Classical ContDiff Topology
variable {G:Gauge}{χ : ChartRatio G} {i j:ℕ} {n:Side}
  {A X:Type} {p : A → Bool}

section Ring
-- coefficientwise polynomial conditions
abbrev RankSeries (x : PowerSeries (Coil p ℝ)):=∀ k : ℕ, FinRank (coeff k x)
lemma one_rank : RankSeries (p:=p) 1 := by
  intro k; rw [PowerSeries.coeff_one]; split <;> first| exact FinRank.none| exact FinRank.one
lemma rank_add {x y : PowerSeries (Coil p ℝ)} (h:RankSeries x)(H:RankSeries y): RankSeries (x+y) := by
  intro i; rw [map_add]; exact (h i).add (H i)
lemma rank_mul {x y : PowerSeries (Coil p ℝ)} (h:RankSeries x)(H:RankSeries y): RankSeries (x*y) := by
  intro i; rw [PowerSeries.coeff_mul]; exact FinRank.sum _ _ fun a _=> (h a.1).mul (H a.2)
lemma rank_pow {x : PowerSeries (Coil p ℝ)} (h:RankSeries x) (j:ℕ): RankSeries (x^j) := by
  induction j with|zero=> simpa using (one_rank (p:=p))|succ j ih=> rw [pow_succ]; exact rank_mul ih h
lemma low_pow {R : Type*} [Semiring R] {x:PowerSeries R} {j i:ℕ} (h:coeff 0 x=0) (he:i<j): coeff i (x^j)=0:= by
  induction j generalizing i with
  | zero=> omega
  | succ j ih=> rw [pow_succ,PowerSeries.coeff_mul]; refine Finset.sum_eq_zero fun k hk=>?_ ; by_cases hv:k.2=0; rw [hv,h,mul_zero]; rw [ih (by obtain hz:= Finset.mem_antidiagonal.mp hk; omega), zero_mul]

def exponent (x : PowerSeries (Coil p ℝ)) : PowerSeries (Coil p ℝ) :=
  PowerSeries.mk (fun i=>∑ j∈ Finset.range (i+1),(j.factorial:ℝ)⁻¹ • coeff i (x^j))
@[simp]
lemma exponent_zero (x : PowerSeries (Coil p ℝ)) : coeff 0 (exponent x)=1:= by
  rw [exponent,PowerSeries.coeff_mk]; simp
lemma rank_exp {x : PowerSeries (Coil p ℝ)} (h:RankSeries x): RankSeries (exponent x):= fun i=> by
  rw [exponent, PowerSeries.coeff_mk]; exact FinRank.sum _ _ fun j _=> (rank_pow h j i).smul _
end Ring
local notation "R"=> Complex.ofRealHom
local notation "Ra" => LightQ G n ℝ
local notation "pL" => σbranch (G:=G) (n:=n)
variable (h:LocalRatio χ)

def landauInteraction (h:LocalRatio χ)(n:Side) : PowerSeries (LightQ G n ℝ):=
  PowerSeries.mk fun i=> if i=0 then 0 else logAlphabet h n i

def columnSeries (p : Pace (deck n) G) : PowerSeries (LightQ G n ℝ) :=
  PowerSeries.mk fun i=> rankn (i+p.k) (Inlay.bare (I:=Site n) p.intent.caseG)
abbrev landauDensity (h:LocalRatio χ) (n:Side) := exponent (landauInteraction h n)

def siteWick (p:A→Bool) [Fintype A] (H:A→A→ℝ) (F:PowerSeries (Coil p ℝ)):PowerSeries ℝ := PowerSeries.mk fun i=> wither H Finset.univ (coeff i F) []

def landauNumer (h:LocalRatio χ) (stamps : List (Pace (deck n) G)) :=
  siteWick ø (extoll G n 1).hop (landauDensity h n * (stamps.map columnSeries).prod)
abbrev landauVacuum (h:LocalRatio χ)(n:Side):PowerSeries ℝ:= landauNumer (n:=n) h []
/-- Entire all-order moment series at once. `columnSeries` handles its Laurent prefactors
 ($g^{-p.k}$), so return value has no negative powers. -/
def landauPrimary (h:LocalRatio χ) (F : List (Pace (deck n) G)):= (landauVacuum h n)⁻¹ * landauNumer h F

lemma rank_h (x: LightQ G n ℝ)(i:ℕ):FinRank (rankn i x):=⟨_,(rankn.heg x i).cap _ _⟩
lemma rank_i : RankSeries (landauInteraction h n):= by
  intro i; rw [landauInteraction,PowerSeries.coeff_mk]; split; exact FinRank.none; exact (FinRank.add (FinRank.neg (rank_h ..)) (rank_h ..)).smul _
lemma rank_column (p:Pace (deck n) G) : RankSeries (columnSeries p):= fun i=> by rw [columnSeries,PowerSeries.coeff_mk]; exact rank_h ..
lemma rank_press (s: List (Pace (deck n) G)): RankSeries (s.map columnSeries).prod:= by induction s with| nil=> exact one_rank|cons t s ih=> exact rank_mul (rank_column t) ih
lemma pays (s: List (Pace (deck n) G)): RankSeries (landauDensity h n * (s.map columnSeries).prod):= rank_mul (rank_exp (rank_i h)) (rank_press _)
lemma even_stamp (s:Pace (deck n) G) (i:ℕ) : EvenT (coeff i (columnSeries s)):= by
  rw [columnSeries,PowerSeries.coeff_mk]
  intro l he; apply Inlay.bare_h (I:=Site n) _ l; intro hh; apply he; rw [rankn_read,hh]; simp
lemma vacuum_lead : coeff 0 (landauVacuum h n)=1 := by
  unfold landauVacuum landauNumer siteWick; rw [List.map_nil, List.prod_nil,mul_one, PowerSeries.coeff_mk, exponent_zero, show wither _ Finset.univ (1:Ra)=1 from (wither_const (k:=(extoll G n 1).hop) 1)]; rfl
lemma landau_normal (F:List (Pace (deck n) G)) : landauVacuum h n * landauPrimary h F = landauNumer h F := by
  rw [landauPrimary,← mul_assoc, PowerSeries.mul_inv_cancel _ ?_,one_mul]; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,vacuum_lead]; exact one_ne_zero
lemma landau_empty : landauPrimary h (n:=n) [] = 1:= by apply PowerSeries.inv_mul_cancel; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,vacuum_lead]; exact one_ne_zero

-- ascending MS.Puff step
section Puff
local notation "K" => Master G n true
local notation "Θ" => PermV pL

def broadcastSymbol : Ra →+ Koszul.Raw (FixedMode G n) ℂ :=
  ((symbols σbranch ℂ).comp encodeMomentum).toAddMonoidHom.comp (Wind ø R).toAddMonoidHom
lemma broadcastSymbol_c (x:Ra)(u:ℝ): broadcastSymbol (u • x)= (u:ℂ) • broadcastSymbol x := by
  change symbols _ _ (encodeMomentum (Wind _ _ _))= (u:ℂ) • symbols _ _ (encodeMomentum (Wind _ _ _)); rw [Wind_smul,map_smul,map_smul]; rfl
lemma broadcastSymbol_m (x y: Ra): broadcastSymbol (x*y)=MS.Koszul.product pL (broadcastSymbol x) (broadcastSymbol y) := by
  change symbols _ _ (shot _ _ legalChange (Wind _ _ _))=_; rw [map_mul,shot_mul,symbols_mul]; rfl

def broadcastSeries (F:PowerSeries (LightQ G n ℝ)) : Orbit.LogReal.SpecB (FixedMode G n) := fun i=> broadcastSymbol (coeff i F)
local notation "B" => broadcastSeries
lemma broadcast_one : broadcastSeries (G:=G) (n:=n) 1= (Θ).unit:= by
  funext k; have he:broadcastSymbol (1:Ra)=Koszul.coin 1:= by change symbols _ _ (encodeMomentum (Wind _ _ _))=_; rw [map_one,show encodeMomentum (n:=n) (G:=G) 1=1 from (shot_put ..),symbols_one]
  change broadcastSymbol (coeff k 1)=useN.refineV _ k
  rw [PowerSeries.coeff_one]; unfold Puff.SplitP.refineV; by_cases ht:k=0
  · rw [if_pos ht,if_pos (show k= useN.origin from ht),he]; rfl
  rw [if_neg ht,if_neg (show k≠ useN.origin from ht),map_zero]
lemma broadcast_mul (x y : PowerSeries (LightQ G n ℝ)): B (x*y)= (Θ).core (B x) (B y) := by
  funext i; change broadcastSymbol _=_; rw [PowerSeries.coeff_mul,map_sum]; exact Finset.sum_congr rfl fun _ _=> broadcastSymbol_m ..
lemma broadcast_pow (x:PowerSeries (LightQ G n ℝ))(j:ℕ): B (x^j)= (Θ).power (B x) j:= by
  induction j with
   | zero=> simpa only [pow_zero,Actors.power] using (broadcast_one (G:=G) (n:=n))
   | succ j ih=> rw [pow_succ', broadcast_mul, ih]; rfl
lemma broadcast_exp (x : PowerSeries (LightQ G n ℝ)) : B (exponent x)=exp0 pL (B x) := by
  funext i; change broadcastSymbol _= (((Θ).cheers _ i) i); rw [exponent,PowerSeries.coeff_mk,map_sum,Actors.cheers,Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_
  rw [Actors.wages, ← broadcast_pow]
  rw [broadcastSymbol_c, Pi.smul_apply]; unfold Actors.phase; push_cast; rfl

abbrev complex_coeff (x:PowerSeries ℝ) : ℕ→ℂ := fun i=> ↑(coeff i x)
local notation "Σ↓"=> complex_coeff
lemma complex_mul (x y:PowerSeries ℝ) : Σ↓ (x*y)= Trunk.core (Σ↓ x) (Σ↓ y) := by
  funext i; rw [complex_coeff,PowerSeries.coeff_mul]; push_cast; rfl
lemma earth (F:PowerSeries (LightQ G n ℝ)) (he:RankSeries F) : ℶV K (B F)=complex_coeff (siteWick ø (extoll G n 1).hop F):= by
  funext i; rw [complex_coeff,siteWick,PowerSeries.coeff_mk]; exact real_view _ (he i)
lemma broadcast_even {F : Ra} (hx: Coil.Tone false F): Koszul.Pure pL false (broadcastSymbol F) :=
  symbols_pure (Tome_approve (H:=legalChange) (show Coil.Tone false (Wind ø R F) from Tone.seep false F (Complex.ofRealHom.toAddMonoidHom) hx))
lemma broadcast_guard (F:Pace (deck n) G): B (columnSeries F) ∈ (Θ).guard := fun i _=> broadcast_even (even_stamp F i)

/-- This is a true ratio equality (in particular for positive mark degree).
 Follow with geometry and shift theorems to identify physical input, not just core/wires. -/
theorem native_to_Endμ (s:List (Pace (deck n) G)) : Endμ K pL (B (landauInteraction h n))
    (B (s.map columnSeries).prod) (complex_coeff (landauPrimary h s)) := by
  unfold Endμ; rw [← broadcast_exp,← broadcast_mul,earth _ (pays h s)]
  have he:= earth (landauDensity h n) (rank_exp (rank_i h))
  change ℶV _ _= _ at he; rw [he,← complex_mul]; have hc : siteWick ø (extoll G n 1).hop (landauDensity h n)= landauVacuum h n:= by unfold landauVacuum landauNumer; rw [List.map_nil,List.prod_nil,mul_one]
  rw [hc,landau_normal]; rfl
end Puff
end YM.WilsonComparison.Finite
