import YM.MS.High.Iterate
/-!
# All-order induction logical plumbing

Moment tuning only at one h/read rank each time; no loop resummation. Remember
parameters for all previous order coefficients. These are helper lemmas, not the
local classification condition a construction needs to provide. `Data` families
parameter type arbitrary, family encodes vertex metadata & all choices; previous F
on a code unaffected by tuning higher. Any orbit/energy selection independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G : Gauge} {h q v:ℤ} {r s d n:ℕ} {b : Bool} {U:ℕ→Type} {E:Type}
abbrev Code (U : ℕ→Type):= ∀ n,U n
structure Knobs (U : ℕ→Type) (G : Gauge) where
    wake (p : Code U) : Recount G
    stay (p q) (n) (h:∀ i≤n,p i=q i): wake p n=wake q n
namespace Knobs
-- never assume availability of big gain changes on whole kernels, only patch of jets. Quantify coherent choices.
variable {k : Knobs U G} {P Q T:Code U} {G': Recount G}
def Same (B : Reading G) (b : Bool) (r:ℕ) (F:Reading G): Prop:= ∀ y w, Course b w→ w.length=r → B y w= F y w
structure Stroke (b:Bool) (k:Knobs U G) (P Q:Code U) (n r:ℕ): Prop where
    past i:i< n→ P i=Q i -- typo i
    memory s (p:r<s): Same (k.wake P n) b s (k.wake Q n)

lemma Stroke.of_refl : Stroke b k P P n r:= ⟨fun _ _ => rfl, fun _ _ _ _ _ _=> rfl⟩
lemma Stroke.trans (H : Stroke b k P Q n r) (K : Stroke b k Q T n r): Stroke b k P T n r:=
    ⟨fun i p=> (H.past i p).trans (K.past i p), fun s hs i w hp hx=> (H.memory s hs i w hp hx).trans (K.memory s hs i w hp hx)⟩
lemma Stroke.permit (H : Stroke b k P Q n r) (x : r≤s): Stroke b k P Q n s:= ⟨H.past,fun j h=> H.memory j (lt_of_le_of_lt x h)⟩
-- compare actual Taylor coefficients of new lattice vertices. All LogTime, no Taylor condition elsewhere.
structure Move (b:Bool) (k : Knobs U G) (P Q: Code U) (n r : ℕ) (v:ℤ) (Y: ℝ→ Law G): Prop extends Stroke b k P Q n r where
    tune y t w (p:Course b w) (hs:w.length=r) (j:ℕ) (h: fieldDim wfield w+j≤v) : torch j (k.wake Q n (y,t)) w = torch j (k.wake P n (y,t)) w - if fieldDim wfield w+j=v then Y y w else 0

lemma Move.refl (Y:ℝ→Law G) (h : ∀ y w, Course b w→ w.length=r → Y y w=0) : Move b k P P n r v Y:= ⟨Stroke.of_refl,fun y t w hw hx j h'=> by rw [h y w hw hx]; simp⟩
lemma Move.replace {K L : ℝ→Law G} (he : Move b k P Q n r v K) (ht:∀ i w, Course b w→ w.length=r→ L i w=K i w) : Move b k P Q n r v L:= ⟨he.toStroke, fun i t w h hx j hz=>by rw [ht i w h hx]; exact he.tune i t w h hx j hz⟩
-- Momentum-wise. Doesn't assert equality of any vertex with off Course extension.
def Fixed (P : Recount G) (F : Recount G) (b : Bool) (h : ℤ) (d : ℕ) := ∀ n, d ≤ n → ∀ r, fig b r → Trust b h (P n) (F n) r
def EarlierOrder (b : Bool) (P : Recount G) (F : Recount G) (h : ℤ) (d n : ℕ) := ∀ i, i<n → d ≤ i → ∀ r, fig b r→ Trust b h (P i) (F i) r
def Ahead (b : Bool) (P F : Recount G) (h : ℤ) (d n r : ℕ) := EarlierOrder b P F h d n ∧ ∀ s, r<s→ Trust b h (P n) (F n) s

lemma alive {F K K': Reading G} {r : ℕ} (he : Same F b r K) (hX : Trust b h F K' r): Trust b h K K' r:= match_agrees meet.primary b (fun i=> he (index i,t i)) (fun _ _ _ _=> rfl) hX
lemma Sterile {F:Recount G} (X: Stroke b k P Q n r) (he: EarlierOrder b (k.wake P) F h d n): EarlierOrder b (k.wake Q) F h d n := by
   intro i hi hx j hv; rw [← k.stay P Q i (fun u hu=>X.past u (lt_of_le_of_lt hu hi))]; exact he i hi hx j hv
lemma ahead {F:Recount G} (X: Stroke b k P Q n r) (he: Ahead b (k.wake P) F h d n r): Ahead b (k.wake Q) F h d n r:= ⟨Sterile X he.1, fun i hi=> alive (X.memory i hi) (he.2 i hi)⟩

-- ready use after sampling; adjust rank n here.
lemma zero_absent (F : Reading G): Absent F b r 0:= fun w h x j hj u=> by exfalso; have he:=Detect.length_pay (G:=G) w; omega
lemma torch_sub {M W:Law G} (w : List (Lane4 G)) (hf : ContDiff ℝ ∞ (fieldVal M (ray w))) (hg : ContDiff ℝ ∞ (fieldVal W (ray w))) j : torch j (M-W) w= torch j M w- torch j W w:= by
    simp_rw [torch_at,Pi.sub_apply]; unfold reading; unfold fieldVal at hf hg; rw [iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top)), smul_sub]

-- pay after slicing (v already absent below)
variable (hs : d≤n) (ht : fig b r) {C : ℂ} {B: Code U→Recount G} {B' D':Recount G}
   (p : ∀ ζ:Code U,Spheres wave (spaceL G) (B ζ) (k.wake ζ) C d b) (L : Spheres id (spaceD G) B' D' C d b)
include p L hs ht
lemma accept (X : Move b k P Q n r v (slice (k.wake P n-D' n) b r v)) (hE : Earlier (B P) B' (k.wake P) D' b h n d r) (hq : v≤h) (hv:Absent (k.wake P n-D' n) b r v): Absent (k.wake Q n-D' n) b r (v+1):= by
    intro w hx hz j he u; let R:=ray w; have hR:Course b R:= ray_course hx
    have hU : Used b R:= fun h=> by rw [show List.length R=r from (ray_len ..).trans hz]; exact ht h
    have h0 (i : Code U) (y:ℝ×ℝ) : ContDiff ℝ ∞ (fieldVal (k.wake i n y) R):= (((p i).road ℝ R n hs hU) hR).1 y
    have hT (y:ℝ×ℝ): ContDiff ℝ ∞ (fieldVal (D' n y) R):= ((L.road ℝ R n hs hU) hR).1 y
    let d':= fieldDim wfield w+j; have he' : d' ≤ v := by unfold d'; omega
    let V (t:ℝ):= torch j ((k.wake P n - D' n) (u,t)) w
    let a:=slice (k.wake P n - D' n) b r v u w
    have hm (t:ℝ): torch j ((k.wake Q n-D' n) (u,t)) w= V t-if d'=v then a else 0:= by
       unfold V; rw [Pi.sub_apply, torch_sub w (h0 Q (u,t)) (hT ..), X.tune _ _ _ hx hz j he', Pi.sub_apply, torch_sub w (h0 P (u,t)) (hT ..)]; exact sub_right_comm ..
    simp_rw [hm]; obtain h1|h1:= lt_or_eq_of_le he'; · rw [if_neg (ne_of_lt h1)]; simp only [sub_zero]; exact hv w hx hz j h1 u
    rw [if_pos h1]; let hq:= slice_torch (advanced (p P) L hs ht hE) u hx hz (show fieldDim wfield w+j=v from h1) hq
    exact (by simpa [V,a] using hq.sub_const a)
end Knobs
end YM.MS.High
