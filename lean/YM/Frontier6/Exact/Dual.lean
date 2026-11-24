import YM.Frontier6.Pair.Paths
import YM.Frontier6.Exact.Words

/-!
# Plane gains through to continuum: tested pair fusion against all phases

Do this first in dual form (allows both signs and complex coefficients in the
readout; doesn't assume detection on a fixed time slice; the annihilation can
use *different* phases). Ext-family indices arbitrary finite. Slots, norms and
the same physical tags persist. Strict seam margins before O(4) argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Extraction.Lease Cells Extraction.Around OS Word MeasureTheory Org Canvas Platform
open Next.Extract Dash PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}
variable (K:Final C F S){D d b :ℕ}(B:S.Field d)(P:S.Field b)
variable {I:Type*}[Fintype I]{n:I→ℕ}

/-- Dual exteriors as finite tuples with position parameters. Vary the
positions and numeric coefficients in estimates; labels separately can always
first be expanded in fixed finite bases. -/
abbrev Tuple (S:Table C.book)(n:I→ℕ) := (i:I)→ Fin (n i) → S.Tag
abbrev Seen (n:I→ℕ) := (i:I)→ Points (n i)
variable (v:Tuple S n)

def kills (y:Seen n)(u:I→StateIndex K)(c:I→ℂ)(w:ℕ):Prop:= ∀ e<w, ∀ x:S.Field e, ∑ i:I,c i * reading K (u i) 0 (y i) (v i) e x=0

def listen (y:Seen n)(u:I→StateIndex K)(c:I→ℂ)(x:E4):=∑ i:I,c i* pairRead K (u i) B P (v i) x 0 (y i)

def shapes (r:ℝ)(y:Seen n):= ∀ i, clearC r (y i)

def noSeam (S:Schedule) (k:ℕ)(g:ℝ)(y:Seen n):Prop:=∀ i, ∃ c:Fin (n i)→ Lattice.Cover, Injective (Fin.cons (α:=fun _:Fin (n i+1)=> Lattice.Cover) 0 c) ∧ ∀ j,atStop S k (c j) g (y i j)

section offSeam
variable {w:ℕ}{H:Table C.book}{M:ℕ→Table C.book}{Q:Bin H}{Y:DiffPlan S} (h:Base C F H M Q S Y) (hp:PairProducer C) (hg:G.Simple) (hW:Extraction.Wcmain C)(hG:Grill C F)

include h hp hg hW hG
set_option quotPrecheck false
local notation "R"=>fuga C.path.levels
/-- Extend placement from sparse pairs. Strict off-seam layout first.
Completely independent of moving exterior positions/states with these tests.
Working at horizon D requested by left functionals; one can take D much higher,
but error in gradient interpolation must then also pay corresponding finer powers. -/
lemma grid_dual {A g r:ℝ}(ha:0 ≤ A)(hx:0 < g)(hr:0 < r){ε s δ:ℝ} (hs:1<s)
   (hε:s*(d+b:ℝ)+8*(s-1) < d+b+ε) (hd : δ+s*(d+b:ℝ)+8*(s-1)<1/8+(d:ℝ)+(b:ℝ))(hδ:0 < δ)
   (k:ℕ)(hk:C.ref w≤ k){j:ℕ→ℕ} (hh:∀ᶠ i in atTop,i+1<j i)(hj:Tendsto j atTop atTop)(hs':Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 s)) :
   ∀ᶠ i:ℕ in atTop, ∀ x∈ {x:E4| R (i+1)/16 ≤ ‖x‖ ∧ ‖x‖≤4*R i}, MergeProof.Acme.taper (C.S.a (j i)) x=Set.univ→ ∀ (y:Seen n), shapes r y→ noSeam C.S k g y→ (∀ p,Points.cons x (Points.cons 0 (y p))∈conf (n p+2)) → ∀ (u:I→StateIndex K)(c:I→ℂ), (∀ p,‖c p‖≤ A) → kills K v y u c w →
     ‖listen K B P v y u c x‖ ≤ Real.exp (((d:ℝ)+b-w+ε)*C.S.scale i):=by
    let B':=S.representative _ B; let P':=S.representative _ P
    let S':= C.S; let cPage:C.label w →L[ℂ] S.Field w:= LinearMap.toContinuousLinearMap (S.project w); let V:=((d:ℝ)+(b:ℝ))*s+8*(s-1)
    obtain ⟨a,f,ha',hf,hv⟩:=grid_output hp hW hg h K (η:=δ) (by linarith only [hd]) hk hh hj hs' B' P' -- fix hδ
    choose U hu hY using fun i:I=> contexts (D:=w) B' P' K hG (Ward.expose ∘ v i) g hx k
    choose T hT hV using fun i:I=> reading_bounded K hG (v i) r hr w
    let Y p:= A*U p; let Z p:= A*T p*‖cPage‖; let Y':=1+∑ p,Y p; let Z':=1+∑ p,Z p
    let t x:= Real.exp (((d:ℝ)+b-w+ε)*C.S.scale x)
    let z m:= voyage C w m 0*f m
    have hE: (d:ℝ)+ b ≤ V:=by unfold V; nlinarith only [hs,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) b]
    have hF:Note C.S (fun i=> (1/2:ℝ)*t i) ((d:ℝ)+b-w+ε):= by exact ((Note.notes C.S _ (by norm_num:0<(1/2:ℝ))).mills (Note.bell_exp ..)).swapP (by ring)
    have hZ:Note C.S z (-w+V):=((voyage_pitch C w 0).mills hf).swapP (by push_cast; dsimp only [V]; ring)
    have hA': 0 ≤ ∑ p,Y p:= Finset.sum_nonneg fun i _=> mul_nonneg ha (hu _|>.le)
    have hB': 0 ≤ ∑ p,Z p:= Finset.sum_nonneg fun i _=> mul_nonneg (mul_nonneg ha (hT _)) (norm_nonneg cPage)
    have hε : V < _:= show V < d+b+ε from (by dsimp only [V]; linarith only [hε]) -- fix
    filter_upwards [hv,(ha'.mills (Note.notes C.S _ (show 0<Y' from by unfold Y'; linarith only [hA']))).outweigh hF (by linarith only [hE,hε,hδ]),(hZ.mills (Note.notes C.S _ (show 0<Z' from by unfold Z'; linarith only [hB']))).outweigh hF (by linarith only [hε]), hj.eventually_ge_atTop k] with i hi h₁ h₂ hhk x hx' he y hh' hS hc s c hC hu'
    obtain ⟨x',rfl,hx⟩:=MergeProof.Acme.read_grid (C:=C) he; let y':= C.S.gridPoint (j i) x'
    obtain ⟨L,hL,hPage⟩:= hi _ hx'.1 hx'.2; obtain ⟨ℱ,hf,hN,hX⟩:= hL.retires
    have ht : ∃ L':C.label w, ‖L-L'‖ ≤ z i ∧ ∑ p:I, c p* reading K (s p) 0 (y p) (v p) w (S.project _ L')=0:=by
        cases w with
        | zero=> refine ⟨0,?_,?_⟩; simpa using! hPage.whole; simp
        | succ w=>
           obtain ⟨v',⟨B,hB⟩,hg⟩:= hPage.below w w.lt_succ_self
           refine ⟨v',?_,?_⟩;simpa using hg -- voyage sub
           rw [← hB]; simp_rw [reads_at, (fun p=>(inception K (s p)).kernels w.le_succ B (gap_conf hr.le (hh' p)) (v p)), ← reads_at]; exact hu' w w.lt_succ_self B
    obtain ⟨L',hz,h⟩:=ht
    let S(p):= reading K (s p) 0 (y p) (v p) w
    let Q(p:I):= pairRead K (s p) B P (v p) y' 0 (y p)
    have hr'(p:I): ‖Q p-S p (cPage L)‖ ≤ a i * U p:=by
        obtain ⟨d,h₀,h₂⟩:= hS p
        have ht:= hY p ℱ hN (a i) (ha'.pos _|>.le) hf _ hhk _ _ hX hx d h₀ (y p) h₂ (hc p) (s p) -- b ≤ j? check
        rw [show S p (cPage L)=_ from cost_unit K (s p) _ _ (v p) w _ (Points.tail_in (hc p)), show Q p= _ from pair_actual K (s p) B P (v p) y' 0 (y p)]
        exact ht
    have hr₂(p:I) : ‖S p (cPage (L-L'))‖ ≤ T p* ‖cPage‖ * z i:=by
       apply ((S p).le_opNorm _).trans; rw [mul_assoc]
       apply mul_le_mul (show ‖S p‖ ≤ T p from hV p (s p) _ _ (hh' p)) ((cPage.le_opNorm _).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))) (norm_nonneg _) (hT p)
    unfold listen
    change ‖∑ p:I,c p * Q p‖ ≤ t i; rw [← sub_zero (∑ p:I,_),← h, ← Finset.sum_sub_distrib]
    refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun p:I=> a i*Y p+ z i * Z p) fun p _=> ?_) ?_)
    · change ‖c p * Q p-c p*S p (cPage L')‖ ≤ _
      rw [←mul_sub,norm_mul,show Q p-S p (cPage L')= Q p-S p (cPage L)+S p (cPage (L-L')) by rw [map_sub,map_sub]; abel]; refine (mul_le_mul (hC p) ((norm_add_le ..).trans (add_le_add (hr' p) (hr₂ p))) (norm_nonneg _) ha).trans_eq (?_)
      unfold Y Z; ring
    rw [Finset.sum_add_distrib,← Finset.mul_sum (a:=a i),← Finset.mul_sum (a:=z i)]; dsimp only [Y',Z'] at h₁ h₂
    linarith only [h₁,h₂,ha'.pos i,hZ.pos i]
end offSeam
end YM.Frontier6
