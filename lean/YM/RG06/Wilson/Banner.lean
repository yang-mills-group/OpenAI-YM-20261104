import YM.RG06.Wilson.Inlet

/-! # Symmetries and relabeling of stencil coefficients

Star on physical reality variables, lattice Signed (so includes naive spatial/time
axis reflection before conjugation), global adjoint, and site gauge as a formal-group
identity before log read (no choice of BCH/log domain). No symmetry assumed for
selected gauge-fixed kernel here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonCompiler
open Function Set GSeries Lattice RG Labels Source Wilson
open scoped BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {X V W : Type*} [AddCommGroup X] [One X]
variable {d : ℕ}

/-- Non-mixing address transform on positive link logs, with sign when an orientation reverses. -/
def spinLog (s : Signed) (b : Four X) (u : Links X G.Color) (l : DLink X) :=
  let d := (posDir l.2).rotate s
  if d.neg then - u (d.used (affine s b l.1)) else u (d.used (affine s b l.1))

theorem roll_spin (s : Signed) (b : Four X) (A : Links X G.Color)(r : ℝ) :
    roll (spinLog s b A) r = pull s b (roll A r) := by
  funext i
  unfold roll spinLog pull Step.read
  cases e: ((posDir i.2).rotate s).neg <;> simp only [e,Bool.false_eq_true, ↓reduceIte]
  rw [smul_neg, Work.F03.exp_neg_color]

lemma roll_move {n : Side}(b:Site n)(A:Links (Per n) G.Color)(r:ℝ):roll (translate b A) r=translate b (roll A r):=rfl

theorem top_spin (s : Signed) (A : Links ℤ G.Color) (C : Family G) (h:C.Makes) (p : C.label d):
    develop (access G (spinLog s 0 A)) (markTop C d p) =
      develop (access G A) (markTop C d ((C.labels.level d).act s.ortho p)) := by
  rw [(gasket ..).series, (gasket ..).series]; simp_rw [roll_spin, (h.sections d).Hpart]

theorem site_spin {n:Side} (s:Signed)(b x:Site n)(A:Links (Per n) G.Color)(C:Family G)(h:C.Makes)(p:C.label d):
    develop (access G (spinLog s b A)) (markSite C d p x) = develop (access G A) (markSite C d ((C.labels.level d).act s.ortho p) (affine s b x)) := by
  rw [(orbit ..).series,(orbit ..).series]; simp_rw [roll_spin,(C.localSection d).placed_signed (h.sections d)]

theorem site_moved {n:Side} (b x:Site n)(A:Links (Per n) G.Color)(C:Family G)(p:C.label d):
    develop (access G (translate b A)) (markSite C d p x) = develop (access G A) (markSite C d p (x+b)) := by
  rw [(orbit ..).series,(orbit ..).series]; simp_rw [roll_move,SectionData.places_trans]

theorem site_wrapped {n:Side} (x:Site n)(A:Links (Per n) G.Color)(C:Family G)(p:C.label d):
    develop (access G (expandAt x A)) (markTop C d p) = develop (access G A) (markSite C d p x):= by
  rw [(orbit ..).series,(gasket ..).series]; rfl

-- Real-conjugated coefficients
lemma seriesStar {f: ℝ→ℂ} (p : PowerSeries ℂ) {t:ℝ}(he:Garnish t f p) :
    Garnish t (star ∘ f) (PowerSeries.map (starRingEnd ℂ) p) := by
  let L:= starL ℝ (A:=ℂ)
  have hp:= he.linear (ContinuousLinearEquiv.toContinuousLinearMap L)
  have ht: reCoeff (ContinuousLinearEquiv.toContinuousLinearMap L).toLinearMap p=PowerSeries.map (starRingEnd ℂ) p := by
    ext1 k; rw [coeff_reCoeff,PowerSeries.coeff_map]; rfl
  rwa [←ht]

private lemma series_conj {f g:ℝ→ℂ} {t}{p q:PowerSeries ℂ}
    (hp:Garnish t f p)(hq:Garnish t g q) (he : ∀ r,g r=star (f r)): q= PowerSeries.map (starRingEnd ℂ) p := by rw [hq.series,show g=star∘f from funext he, ← (seriesStar _ hp).series]

theorem developedStar (a : V → ℝ) (P : PowerSeries (Pigment V)):
    PowerSeries.map (starRingEnd ℂ) (develop a P)=develop a (PowerSeries.map (conjugateP V) P):= by
  ext1 k; rw [PowerSeries.coeff_map,develop_coeff,develop_coeff,PowerSeries.coeff_map,tone_conjugate]; rfl

theorem top_star (C : Family G) (h:C.Makes) (p : C.label d):
    markTop C d (star p)= PowerSeries.map (conjugateP (LinkVar G ℤ)) (markTop C d p):= by
  refine folio_ext fun a=> ?_; rw [← developedStar,← access_peel a]; exact series_conj (gasket ..) (gasket ..) (fun _=> (h.sections d).ordinary_real p _)

theorem site_star {n:Side} (C:Family G)(h:C.Makes)(p:C.label d)(x:Site n):
    markSite C d (star p) x=PowerSeries.map (conjugateP (LinkVar G (Per n))) (markSite C d p x):= by
  refine folio_ext fun a=>?_ ; rw [←developedStar,←access_peel a]; exact series_conj (orbit ..) (orbit ..) (fun _=>(h.sections d).ordinary_real p _)

-- Unit structural, literally at each cutoff (basis e0, global unit O in Family)
theorem top_bead (C:Family G)(h:C.Makes)(d:ℕ):markTop C d (C.labels.level d).e0=1 := by
  refine folio_ext fun a=> ?_; rw [← access_peel a,(gasket ..).series,map_one]; simp_rw [(h.sections d).unit]; exact assembler_const .. |>.trans (map_one _)

theorem site_bead {n:Side}(C:Family G)(h:C.Makes)(d:ℕ)(x:Site n):markSite C d (C.labels.level d).e0 x=1:= by
  refine folio_ext fun a=> ?_; rw [← access_peel a,← site_wrapped, top_bead C h]
  simp only [map_one]

-- global color covariance in the physical basis, orientation of `gauge` preserved
theorem spinPaint (g:G.El)(A:Links X G.Color)(t):roll (fun i=>G.adjoint g (A i)) t=gauge (fun (_:Four X)=>g) (roll A t) := by
   funext i; unfold Lattice.gauge roll
   have he : ∀ v:G.Color,G.lieExp (G.adjoint g v)=g*G.lieExp v*g⁻¹ := by
     intro v; apply G.mat_injective; simp only [G.mat_mul,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl
   rw [← LinearMap.map_smul (G.adjoint g),he]

theorem markSite_invariant (C:Family G)(h:C.Makes)(p:C.label d){n:Side}(x:Site n)(A:Links (Per n) G.Color)(g:G.El):
    develop (access G (fun i=> G.adjoint g (A i))) (markSite C d p x)=
      develop (access G A) (markSite C d p x):= by
  rw [(orbit ..).series,(orbit ..).series]; simp_rw [spinPaint,SectionData.placed_invariant _ (h.sections d) x p _ _]

theorem markTop_invariant (C:Family G)(h:C.Makes)(p:C.label d)(A:Links ℤ G.Color)(g:G.El) :
    develop (access G (fun i=>G.adjoint g (A i))) (markTop C d p)= develop (access G A) (markTop C d p):= by
  rw [(gasket ..).series,(gasket ..).series]; simp_rw [spinPaint,(h.sections d).gaugeInvariant p _ _]

section
variable {S : Finset Cover}
-- arbitrary gauge sweeps as group rule using two sets of variables (log at
-- both the original links and gauge transformation). Identifies *entire*
-- g coefficients by gauge invariance BEFORE logs, on Cover first. Formal
-- marker operations with these rings commute by exact equality.
abbrev tinted {X : Type*} (K:DLink X → Animation G V) (e : UsedEdges S→ DLink X) (i : Index G S): PowerSeries (Pigment V) :=
  frameP (K (e i.1)) i.2.1 i.2.2.1 i.2.2.2

def footage (p : Formula G S) (K : DLink ℤ→Animation G V) := compile (tinted K locate) p

def projectedFootage {n : Side}(p : Formula G S) (x : Site n) (K : DLink (Per n)→Animation G V):= compile (tinted K (place x)) p

theorem footage_keep (u : V→ℝ)(f:ℝ→ CoverConfig G)(K : DLink ℤ→ Animation G V) (h : ∀ i, Garnish 0 (fun t=> G.mat (f t i)) (soundtrack u (K i))) (p : Formula G S) : Garnish 0 (fun t=> MvPolynomial.aeval (entry (f t)) p) (develop u (footage p K)) :=
  compile_mark p _ _ (fun i t=> entry (f t) i) _ fun i=> frame_match _ _ _ _ (h (locate i.1))

theorem site_keep (u : V→ℝ){n:Side}(f:ℝ→ Config G n)(K : DLink (Per n)→Animation G V)(h:∀ i,Garnish 0 (fun t=> G.mat (f t i)) (soundtrack u (K i)))(p: Formula G S) (x:Site n) : Garnish 0 (fun t=>MvPolynomial.aeval (entry (expandAt x (f t))) p) (develop u (projectedFootage p x K)) :=
  compile_mark p _ _ (fun i t=>entry (expandAt x (f t)) i) _ fun i=> frame_match _ _ _ _ (h (place x i.1))

def paletteG (G : Gauge)(V : Type*)(ρ : Type*) := ρ → Easel G V
abbrev lawLabel (G : Gauge) (D : Type*) := ((Four D)⊕ DLink D) × G.ColorIndex
def tints (G : Gauge)(D : Type*): Four D → Easel G (lawLabel G D) := fun x=> colorTube G (fun i=> MvPolynomial.X (Sum.inl x,i))
def tinks (G : Gauge)(D : Type*): display G D (lawLabel G D) := fun x=> colorTube G (fun i=> MvPolynomial.X (Sum.inr x,i))

omit [AddCommGroup X] [One X] in
lemma cupRefines (u : lawLabel G X → ℝ) :
    let v (l : Four X ⊕ DLink X) : G.Color := WithLp.toLp 2 (fun i=>u (l,i));
    (∀ l: Four X, picture u (tints G X l)=G.colorMat (v (Sum.inl l))) ∧
    (∀ l: DLink X, picture u (tinks G X l)=G.colorMat (v (Sum.inr l))) := by
  constructor <;> intro l <;> (apply colorTube_eval; intro i; simp [tone]) -- rfl?

def rinse (k : DLink X→ Animation G V) (Z:Four X→Easel G V)(d:DLink X) :=
  logRoll (Z d.1) * k d * logRoll (- Z (d.1+step d.2))

theorem washout (u:V→ℝ) (k:DLink X→Animation G V) (f:ℝ→Links X G.El)(Z:Four X→Easel G V)(B:Four X→G.Color)
    (hk:∀l,Garnish 0 (fun t:ℝ=>G.mat (f t l)) (soundtrack u (k l)))(he:∀i,picture u (Z i)= G.colorMat (B i))(l:DLink X):
    Garnish 0 (fun t:ℝ=> G.mat (gauge (fun i=>G.lieExp (t • B i)) (f t) l)) (soundtrack u (rinse k Z l)) := by
  unfold Lattice.gauge rinse
  have hx : ∀ v:Easel G V, picture u (-v)=-picture u v:= map_neg _
  have hB (i:Four X):= link_beat u _ _ (he i)
  have hb (i:Four X):= link_beat u (-Z i) (G:=G) (-B i) (by rw [hx,he,map_neg])
  rw [map_mul,map_mul]; simp_rw [G.mat_mul,← Work.F03.exp_neg_color,← smul_neg]
  exact ((hB _).mul (hk l)).mul (hb _)

-- free site gauge parameters; after expansion, compare polynomial coefficient
-- data on all these parameters. This formulation uses only matrix series
-- products (no diagram recurrences).
theorem markTop_wash (C:Family G)(h:C.Makes)(p:C.label d) :
    let P := (C.localSection d).evalC p
    let k := fun l => logRoll (tinks G ℤ l)
    footage P (rinse k (tints G ℤ))= footage P k := by
  intro P k; apply folio_ext; intro a
  let v (z : Four ℤ ⊕ DLink ℤ) : G.Color:=WithLp.toLp 2 (fun i=> a (z,i))
  let J := fun (l : DLink ℤ) => v (Sum.inr l)
  let V : Four ℤ→G.Color := v ∘ Sum.inl
  let f : ℝ → CoverConfig G:= roll J
  obtain ⟨e,e'⟩:=cupRefines a
  have he:= fun i=> link_beat a (tinks G ℤ i) (J i) (e' i)
  let g (r:ℝ) (i:Four ℤ):=G.lieExp (r • V i)
  have hV := fun i=> washout a k f (tints G ℤ) V he e i
  have ht:= (footage_keep a (fun r=> gauge (g r) (f r)) _ hV P).series.trans
    ((congrArg (assembler 0) (show (fun t=> (C.localSection d).evaluate p (gauge (g t) (f t)))=(fun t=> (C.localSection d).evaluate p (f t)) from funext fun t=> (h.sections d).gaugeInvariant p _ _)).trans
      (footage_keep a f k he P).series.symm)
  exact ht

theorem markSite_wash {n : Side} (C:Family G)(h:C.Makes)(p:C.label d)(o:Site n) :
    let P := (C.localSection d).evalC p
    let k := fun l => logRoll (tinks G (Per n) l)
    projectedFootage P o (rinse k (tints G (Per n)))= projectedFootage P o k := by
  intro P k; apply folio_ext; intro a
  let v (z : Four (Per n) ⊕ DLink (Per n)) : G.Color:=WithLp.toLp 2 (fun i=> a (z,i))
  let J := fun (l : DLink (Per n)) => v (Sum.inr l)
  let V : Four (Per n) → G.Color := v ∘ Sum.inl
  let f : ℝ → Config G n:= roll J
  obtain ⟨e,e'⟩:=cupRefines a
  have he:= fun i=> link_beat a (tinks G (Per n) i) (J i) (e' i)
  let g (r:ℝ) (i:Site n):=G.lieExp (r • V i)
  have hV := fun i=> washout a k f (tints G (Per n)) V he e i
  have ht:= (site_keep a (fun r=> Lattice.gauge (g r) (f r)) _ hV P o).series.trans
    ((congrArg (assembler 0) (show (fun t=>(C.localSection d).places p o (Lattice.gauge (g t) (f t)))=(fun t=> (C.localSection d).places p o (f t)) from funext fun t=> (C.localSection d).placed_invariant (h.sections d) o _ _ _)).trans
      (site_keep a f k he P o).series.symm)
  exact ht
end
end YM.RG06.WilsonCompiler
