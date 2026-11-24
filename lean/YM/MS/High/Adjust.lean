import YM.MS.High.Landing
/-!
# The local tables **as polynomials in the second scale**

At each grade, interpolate with real linear maps using one family of nodes.
Closure gives this on actual physical basis only. No evanescent counterterm
being taken in the lattice regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color Local.Physical Knobs
open scoped Topology ContDiff
variable {G: Gauge} {h r :ℤ} {n v :ℕ} {L H F : Law G} {Y : ℝ → Law G} {M : Reading G} {U: ℕ→Type} {k:Knobs U G} {P: Code U}
lemma mark_inter (hp : Ready Y) (hx : ∀ i, Y i∈Lease G h n 0) (he:∀ i,natQ (Y i)=0) (L:Deck G) : ∃ p q:ℝ→ Law G, Ready p∧Ready q ∧ (∀ i,p i∈L.carries h n)∧(∀ i,q i ∈Lease G (h-1) n (-1)) ∧ Y=fun i=>p i+natQ (q i):= by
    obtain ⟨N,hN⟩:= hp; choose P hP Q hQ h using fun i=> L.select (hx i) (he i)
    refine ⟨evaluate N P,evaluate N Q, eval_ready .., eval_ready ..,fun i=> Submodule.sum_mem _ (fun j _=> Submodule.smul_mem _ _ (hP _)),fun i=> Submodule.sum_mem _ (fun j _=> Submodule.smul_mem _ _ (hQ _)),?_⟩
    funext i; rw [interpret hN i]; unfold evaluate; change _= _ + kills G _; simp_rw [map_sum,map_smul,← Finset.sum_add_distrib, ← smul_add,show ∀ x, P x + kills G (Q x)=Y x from h]

lemma rankzero (l): ranktwo (G:=G) 0 0 l=0:= by
    rcases l with _|⟨l, _|⟨r,_|a⟩⟩ <;> first | rfl| skip
    rw [ranktwo]; split; swap; rfl
    rcases l with ⟨⟨⟨_|l,_|_⟩,i⟩,p⟩ <;> rcases r with ⟨⟨⟨_|r,_|_⟩,j⟩,q⟩ <;> simp [kinds]
private lemma kit (i j : Atom Axis) (p:FourP) (w : ℕ) (f g : ℝ→ℝ) (s:ℝ) : kinds (evaluate w f s) (evaluate w g s) i j p=evaluate w (fun x=>kinds (f x) (g x) i j p) s:= by
    unfold evaluate; rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;>
       simp [kinds,Complex.ofReal_sum,Finset.sum_mul,Finset.mul_sum] <;>
       (apply Finset.sum_congr rfl; intro k _; ring)
lemma pair_inter (hK:G.Simple) (hp:Ready Y) (hv:∀ i, Class (Y i) 4): ∃ p q:ℝ→ℝ, Ready p∧Ready q ∧ ∀ i, EqualAt 2 (Y i) (ranktwo (p i) (q i)):= by
   obtain ⟨N,hN⟩:=hp; choose p q hp0 hp using fun i=> pair_class (hv i) hK (le_refl _)
   refine ⟨evaluate N p,evaluate N q,eval_ready ..,eval_ready .., fun i w he hj=>?_⟩
   rw [interpret hN i]; obtain ⟨l,r,rfl⟩ := List.length_eq_two.mp hj
   have he x:= hp x [l,r] he rfl; unfold evaluate; simp_rw [Finset.sum_apply,Pi.smul_apply,he,ranktwo]; split; swap; simp
   exact Eq.symm (kit ..)
lemma lower_at (hK:G.Simple) (hv:h<4) (hq:Class F h) {w : List (Lane4 G)} (he:net w=0) (hP : 0 < w.length) : F w=0:= by
   generalize hL:w.length=q; have hx:1≤q:=hL ▸ hP
   rcases lt_or_ge q 4 with h1|h1
   · interval_cases q
     · obtain ⟨x,rfl⟩:= List.length_eq_one_iff.mp hL; exact hq.single hK x he
     · obtain ⟨a,b,h,ht⟩:=pair_class hq hK hv.le; specialize ht w he hL; obtain ⟨rfl,rfl⟩:=h.resolve_left hv.ne; exact ht.trans (rankzero w)
     exact Mark.lower_three hq hv w he hL
   exact large_class hq hv.le q h1 w he hL
lemma cube_inter (hK:G.Simple) (H: Class F 4) {v:ℝ} (hv:v≠0) (hx : ∀ i j k, Mark.token F i j k=(Mark.LieColor i j k:ℂ)*(v:ℂ)) (hp : Ready Y) (h:∀ i, Class (Y i) 4): ∃ p:ℝ→ℝ, Ready p ∧ ∀ i, EqualAt 3 (Y i) ((p i:ℂ) • F) := by
    obtain ⟨N,H0⟩:=hp; choose P hp using fun x=> Mark.class_three (h x) H hK v hv hx
    refine ⟨evaluate N P,eval_ready ..,fun i w he hU=>?_⟩
    rw [interpret H0 i]; unfold evaluate; simp_rw [Finset.sum_apply,Pi.smul_apply, hp _ w he hU]; simp [Complex.ofReal_sum,Finset.sum_mul,mul_assoc]

lemma zero_triple_born {B: Recount G} {u:ℤ} (h:u≤4) (S: Spheres wave (spaceL G) B B ((2:ℂ)⁻¹) 1 true) (F' : Recount G) (D : Spheres id (spaceD G) F' F' ((2:ℂ)⁻¹) 1 true) (he : ∀ x w, net w=0 → List.length w=3 → ∀ j:ℕ, fieldDim wfield w+j≤4 → torch j (B 1 x) w=torch j (F' 1 x) w) y w (hd : net w=0) (hq : List.length w=3): slice (B 1-F' 1) true 3 u y w=0:=by
    unfold slice; split; swap; rfl
    have hp : Course true (ray w):= ray_course fun _=>hd; have hR : Used true (ray w):= fun _=> by rw [ray_len,hq]; decide
    let H t:=skin wfield u ((B 1-F' 1) (y,t)) w; have hz (t:ℝ):H t=0:= by
       unfold H skin; split; swap; rfl
       rename_i H; let j:=(u-fieldDim wfield w).toNat
       rw [Pi.sub_apply,torch_sub w (show ContDiff ℝ ∞ _ from ((S.road ℝ (ray w) 1 (le_refl 1) hR hp).1 (y,t))) (show ContDiff ℝ ∞ _ from ((D.road ℝ (ray w) 1 (le_refl 1) hR hp).1 (y,t))), he _ w hd hq _ (by omega),sub_self]
    change limUnder atTop H=0; rw [funext hz]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
end YM.MS.High
