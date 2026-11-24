import YM.X.Chili.Season
/-!
# Reading a grade at any scaled tower at Taylor stage. Supports explicit shelf powers. Travel ≥ R implies Du budget grows.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
-- glyph at mark or vertex
variable {P:ℕ→Brush G}{A:ℕ→Brush G}{F:Rich G}(b:Bool)
def fresh (b:Bool)(z:Fan G): Deck G:= fun _ t=> glyph (Stems.com (leadsL (pace b t) z))
include hq
lemma fresh_read (hr:0≤R)(hF:Grasp F)(f:Fan G)(hf:f∈Reed.grads G m)(hx:k≤d): Visa q R 0 (k-(m+1:ℕ):ℤ) (wreath k d F (fresh b f)):= by
    cases k with
    | zero=> unfold wreath; simp_rw [fresh,footprint₀,map_zero]; exact Visa.zero
    | succ k=> unfold wreath fresh; simp_rw [footprint_proj, if_pos (show k<d from by omega),pillar (Okay G) valP _ _ rfl]; rw [show (((k+1:ℕ):ℤ) - (m+1:ℕ))=(k:ℤ)-m by omega]; simp_rw [taste_eval,lif]; exact (upright (X:=fun i=>F i k) hq b hr (hF k) f hf).com
lemma fresh_exit (hr:0≤R)(hp:R<T')(h:Tide q T' A)(f:Fan G)(hf:f∈Reed.grads G m): Visa q R ((m+1:ℕ):ℤ) 0 (exitP A (fresh b f)):= by
   unfold fresh exitP; simp_rw [carbon]; exact (footprint_field hq b hr hp.le h f hf).com
private lemma scaled_cake (hr:0≤R)(h:Grasp F)(f:Fan G)(hf:f∈Reed.grads G m): Visa q R ((m+1:ℕ):ℤ) 0 (cake d (emerge q F) (fresh b f)):= by
    rw [cake_id]; apply Visa.counts; intro i hi; by_cases hp:i<m+1
    · rw [show wreath i d (emerge q F) (fresh b f)=0 from ?_]; exact Visa.zero
      funext j z; unfold wreath fresh; cases i with
      | zero=> rw [footprint₀,map_zero]; rfl
      | succ i=> rw [footprint_proj,if_pos (show i<d from by simp only [Finset.mem_range] at hi; omega), bloomed (m:=m) (grad_lead (pace b z) f hf) i (by omega), map_zero]; rfl
    have hh := Visa.asPow (c:=(i:ℤ)) (fresh_read (k:=i) (d:=d) hq b hr h f hf (by simpa using hi)); have he : Visa q R i ((i:ℤ)-(m+1:ℕ)) (wreath i d (emerge q F) (fresh b f)):= by
        rw [add_zero] at hh; unfold wreath; simp_rw [emerge,dinner,← zpow_natCast]; exact hh
    exact Visa.stretch hq he hr (by omega) (by omega)
lemma fresh_grove (hr:0≤R)(hp:R<T')(h:Tide q T' A)(he:Grasp F)(hg:Fill (gate q T') (fun i=>ε i^(d+1)) d 0 A (emerge q F))(f:Fan G)(hf:f∈Reed.grads G m): Grove q R A F d (m+1) (fresh b f):= by
    refine ⟨fun p h i hh=> fresh_read hq b hr h f hf hh,?_⟩
    let Q:= emerge q F; let K(i:ℕ)(z:Cover):=flatL (A i-arm d (Q i)) (leadsL (pace b z) f); let P:= exitP A (fresh b f)-cake d (emerge q F) (fresh b f)
    have hh(i:ℕ)(z:Cover) : P i z=(↑(K i z):ℂ):= by unfold P K; rw [Pi.sub_apply,Pi.sub_apply,exitP,cake, fresh,carbon,expel, ← taste_eval, ← taste_eval, ← taste_eval,map_sub,Complex.ofReal_sub]
    have hu : Visa q R ((m+1:ℕ):ℤ) 0 P:= (fresh_exit hq b hr hp h f hf).sub (scaled_cake hq b hr he f hf); change Visa q R _ _ P; rcases lt_or_ge m d with h'|h'
    · refine ⟨?_,fun x hx hr z hz=>?_⟩
      · have ht:Bark (gate q T') (fun i=>ε i^(d+1)) m (d-m) (fun i=> A i-arm d (Q i)):= by simpa only [Nat.add_zero] using! hg m h'.le
        obtain ⟨C,hc,ht⟩:= correction_street (A:=fun i=> A i-arm d (Q i)) hq b hr hp ht f hf; refine ⟨C,hc,?_⟩; filter_upwards [ht] with i hi z hz; rw [hh,Complex.norm_real, Haze.price,zpow_natCast, show (((d+1:ℕ):ℤ)-(m+1:ℕ))=(d-m:ℕ) by omega,zpow_natCast]; simpa only [Real.norm_of_nonneg (pow_nonneg (epsilon_pos q i).le _)] using! hi _ hz
      rw [show (((d+1:ℕ):ℤ)-(m+1:ℕ))-((d+1:ℕ):ℤ)=0-((m+1:ℕ):ℤ) by ring]; exact hu.whereL x hx hr z hz
    exact Visa.stretch hq hu hr (by omega) (by omega)
end YM.PositionX.Clove
