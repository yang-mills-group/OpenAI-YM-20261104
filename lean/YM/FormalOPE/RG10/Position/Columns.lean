import YM.Next.UV_STRESS.Station
import YM.FormalOPE.RG10.Position.Sample

/-! # A version of `check G` on the same real-scheme rails.
Uses the adjusted graded frame, remaining in WilsonX coupling. Measure one before sending to far
horizon; not a proof of a position-scheme rescaling in dimensionally regularized models or on a
different pin history. Includes comparison with the finite regulator ordinary computation in the
same post frame. Establishes the adjustment and a homogeneous scaling equation, *not its
existence without the preadjusted scale law*. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Grade Matrix
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{a b n:ℕ}
local notation "σ" => Profile.n
local notation "T" a => Mark (Deck F a) Profile.n

def dial {I : Type*} (s:ℝ) (p:Mark I σ) : Mark I σ:= ⟨⟨p.1.n,Next.UVStress.dilate (Real.exp_pos (-s)) p.1.test⟩,p.2⟩
-- cumulative Jacobians inside shipped points and tests
lemma move {I:Type*}[Fintype I] (L: Mark I σ→fps) (B:Matrix I I fps) (s:ℝ) : PertExtension.Position.insert I σ (L ∘ dial s) B = PertExtension.Position.insert I σ L B ∘ dial s:=rfl
structure Street {P:Plan F}{Y:Drivers}(Z:Patience P Y)(R:Grade.Rails F) : Prop where
 aligned d s : R.flow.warp s ∘ (fun (v:Mark (Deck F d) Profile.n)=>Z.Yield v) = PertExtension.Position.insert (Deck F d) Profile.n (Z.Yield ∘ dial s) ((R.route d).train s)
-- declaration before using the continuum proofs
namespace Grade.Rails
variable (R:Rails F) {P:Plan F}{Y:Drivers}(Z:Patience P Y)
open Plan Drivers

def adjust (d:ℕ):Mark (Deck F d) Profile.n→fps := PertExtension.Position.insert (Deck F d) Profile.n Z.Yield (R.book d)
def coarse (q : ℕ+)(m d : ℕ) :Mark (Deck F d) Profile.n→fps :=PertExtension.Position.insert (Deck F d) Profile.n (Plan.collect F P q m d) (R.book d)
lemma lifting (v: T a) : Y.Credit (fun q m=> R.coarse (P:=P) q m a v) (R.adjust Z a v):= by
 let b:= R.book a; let u (i: Fin v.1.n → Deck F a) := ∏ j,b (v.2 j) (i j)
 exact Credit.summons (x:=fun (i : Fin v.1.n→ Deck F a) q m=> Plan.collect F P q m a ⟨v.1,i⟩ * u i) (A:=fun i=> Z.Yield (d:=a) ⟨v.1,i⟩ * u i) _ (fun i _=>Credit.cartesian (Z.collected ⟨v.1,i⟩) (Credit.permanent (u i)))
lemma across (hd:a ≤ b): R.adjust Z a = R.adjust Z b ∘ ascend Profile.n (Deck.climb F hd):= by
 have hA : Z.Yield (d:=a)= Z.Yield ∘ ascend σ (Deck.climb F hd):= funext fun v => (Z.larger hd v).symm -- d named?
 unfold adjust; rw [hA]; funext x; rw [← R.scaled_across hd]; apply Eq.symm; apply promote σ (Deck.climb F hd) (R.book b) _ x (Deck.climb_inj F hd);
 intro i j hv; refine (R.route b).booked.1 _ _ ?_; rw [Deck.price_climb];
 have he:= Deck.price_bound F a i
 refine lt_of_le_of_lt he ?_; contrapose! hv; exact Deck.of_price F hd hv

lemma inherits (v : T a) : constantCoeff (R.adjust Z a v)=Physical.free (L:=Maxwell.standard F) (deck F a) v := by
 unfold adjust; rw [insert_constant]; simp_rw [Z.leading];
 have he : (fun i j=>constantCoeff (R.book a i j))=Physical.diag (Deck F a):= by
    ext i j; rw [show constantCoeff (R.book a i j) = _ from coeff_zero_eq_constantCoeff_apply _ |>.symm, ← stamp_apply, Passe.first_base];
    classical
    rw [Matrix.one_apply]; -- diag congr
    by_cases h:i=j<;> simp [Physical.diag,h]
 rw [he]; exact insert_one ..

variable {Z R}
theorem relocation (h:Street Z R) (s:ℝ) :
    R.flow.warp s ∘ R.adjust Z a = PertExtension.Position.insert (Deck F a) Profile.n (R.adjust Z a ∘ dial s) (R.drive s a) := by
 let I:= Deck F a; let g := R.flow
 let P:= R.route a; have he:= h.aligned a s
 let K:= PertExtension.Position.insert (Deck F a) Profile.n (R.adjust Z a ∘ dial s) (P.drive s); change g.warp s ∘ _=K
 calc
  _ = PertExtension.Position.insert (Deck F a) σ (g.warp s ∘ Z.Yield) ((R.book a).map (g.warp s)) := funext fun v=> insert_alg ..
  _ = _:= by
    -- orientation: applying map to outputs recombined first, then using substitution identity
    unfold K adjust g; rw [he,← move (L:=Z.Yield)]; rw [insert_twice,insert_twice]; congr 1
    exact P.describes R.ok s -- maybe defeq
end Grade.Rails
end YM.FormalOPE.RG10.Position
