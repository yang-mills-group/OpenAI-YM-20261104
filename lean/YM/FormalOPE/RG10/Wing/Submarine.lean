import YM.FormalOPE.RG10.Wing.Facets
/-!
 # Generate and evaluate all desired gauge-chart transforms at any finite horizon. Orientation.P
 via replot, nilpotent-vector-field Ward at algebra BEFORE replot. Transfer Step doesn't
 need representative supplied through every `P∈𝒢$` after orientation. Need Open curves.Region. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Submarine
open Function PowerSeries Finset Route Cycle HStein Facets
open scoped Topology BigOperators Classical
variable {I B J : Type} [Fintype I] {k t:ℕ} (u:I→Channel I) (v:I→Channel B)
variable (P:Channel I)

def lane (u:I→Channel I) (k:ℕ) (i:I) := tender u (cycle 1 k) (sprout i)
variable (hu:∀ i, Guard (u i) k 1) (h : steadyDown u)
local notation "A"=> lane u k
local notation "T"=> replot (lane u k)

omit [Fintype I] in
lemma allowed (i:I):Guard (sprout i) k 1:= by
 intro j _; rw [sprout,coeff_C]; split_ifs with he; · simp
 simp
include hu h
lemma foreground (i:I) : Forward u (sprout i) (lane u k i) k:=⟨_, Expiring.above u _ hu h _ (allowed i), Through.refl _⟩
lemma sailing : Forward u P (replot (lane u k) P) k:= by
 have hA (p:Packet I):Forward u (C p) (T (C p)) k:= by
    induction p using MvPolynomial.induction_on with
    | C c=>rw [grain,rules]; apply Forward.ofWard; rw [Derivation.map_algebraMap]; exact Through.refl _
    | add p q hp hq=> rw [map_add,map_add]; exact Forward.add hu h hp hq
    | mul_X p i hp=> rw [map_mul,map_mul,show C (MvPolynomial.X (R:=ℂ) i)=sprout i from rfl, hangs]; exact Forward.mul hu h hp (foreground u hu h i)
 have he (p:Packet I)(k':ℕ): Forward u (monomial k' p) (T (monomial k' p)) k:= by
    rw [radical,map_mul]; refine Forward.mul hu h ?_ (hA p); rw [jag]; apply Forward.ofWard; simp only [Derivation.leibniz_pow,X_charged,smul_zero]; exact Through.refl _
 let p i:= monomial i (coeff i P); have hw (S : Finset ℕ): Forward u (∑ i∈S,p i) (T (∑ i∈S,p i)) k := by
    induction S using Finset.induction_on with
    | empty=> simp only [sum_empty,map_zero]; apply Forward.ofWard; rw [map_zero]; exact Through.refl _
    | insert i S hi ih=> rw [sum_insert hi,map_add]; exact Forward.add hu h (he ..) ih
 exact Forward.congr (hw _) (Facets.paper P k).symm (Facets.through A (Facets.paper P k).symm)
lemma called (he:Expiring u P k t) : Through k (replot (lane u k) P) (tender u t P) := ((sailing u P hu h).latest he).symm
lemma motionless (hp: Through k (kick u P) 0): Through k (replot (lane u k) P) P:= ((called u P hu h (WardGiven u P hp))).trans ((Forward.ofWard hp).latest (WardGiven u P hp))
omit h in
lemma stays (i:I): Guard (lane u k i) k 1:= by
 unfold lane; rw [touch]; exact Guard.sum _ _ (fun t _=> Guard.const_smul (closed_powers u _ hu 1 (allowed i) t) _)
-- leading computation (cycle≥2 attaining exp.P0 linear).
lemma first (a:I) : coeff 0 (lane u k a)=MvPolynomial.X a+ coeff 0 (u a):= by
 have h0 : 2≤ cycle 1 k:= by unfold cycle; nlinarith; -- Nat

 have he : Through 0 (lane u k a) (tender u 2 (sprout a)) := by
    apply Expiring.later (u:=u) (show Expiring u (sprout a) 0 2 from ⟨by decide,?_⟩) h0
    apply (Expiring.above u _ (fun i=> (hu i).less (Nat.zero_le _)) h 1 (allowed a)).2
 have hk : numeral (kick u) 1 (sprout a)=u a:= by rw [show 1=0+1 from rfl,thick_stamp,precise_zero,sprouting]; simp
 rw [he 0 le_rfl,touch]; rw [Finset.sum_range_succ, Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,precise_zero, hk,zero_add,map_add,sprout,coeff_zero_C]
omit hu h
variable (w:I→Channel (I⊕B)) (g:I⊕B→ Channel (I⊕B)) [Fintype B]
-- define pure coarse inputs
abbrev mark (i:I) : Channel (I⊕ B):= sprout (Sum.inl i)
abbrev jewel (b:B) : Channel (I⊕B):= sprout (Sum.inr b)
def craft := Sum.elim w (jewel (B:=B))

def alternate (w:I→Channel (I⊕B)) (g:I⊕B→Channel (I⊕B)) (k:ℕ) (i:I) := replot (craft w) (lane g k (Sum.inl i))
variable (hh: ∀ i,Guard (g i) k 1)(hn:steadyDown g)
include hh hn
-- only Ward equations in the lifted charts, not assumed invariant under non-gauge symmetry.
theorem passenger (hp: Through k (kick g (replot (mark (B:=B)) P)) 0) : Through k (replot w P) (replot (alternate w g k) P) := by
 have he:= Facets.through (craft w) (motionless g _ hh hn hp).symm; rw [Facets.summit, Facets.summit, Facets.summit] at he
 have hj : (fun i:I =>replot (craft w) (mark i)) = w := funext fun i=> hangs (craft w) _
 have hk : (fun i:I => replot (fun v=> replot (craft w) (lane g k v)) (mark i))=alternate w g k:= funext fun i=> hangs _ _ -- depends on summit shapes
 simpa only [hj,hk] using he -- inspect
end YM.FormalOPE.RG10.Wing.Submarine
