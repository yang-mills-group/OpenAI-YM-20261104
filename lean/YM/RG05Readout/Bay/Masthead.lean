import YM.RG05Readout.Bay.Needle
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}(h:C.Makes)
set_option quotPrecheck false
open Extraction
local notation "α!"=> C.S.a
open Metric
open Dash
local notation "R!"=> Fin (n+1)
-- data on the base table.A ready Bank works at ANY d.
structure Poem (C:Family G)(j:ℕ) where
   n : ℕ
   token : Fin n → C.book.Token
   key : Fin (n+1)→ Cover
   centered : key 0=0
   fits : sand (points fun i=>C.S.gridPoint j (key i)) (C.S.a j/16) ⊆ conf (n+1)
namespace Poem
variable (D:Poem C j)
local notation "I"=> Fin D.n
local notation "V0"=> Fin (D.n+1)
noncomputable def template (D:Poem C j) := points (fun i=>C.S.gridPoint j (D.key i))
abbrev reads (D:Poem C j) := Packet D.template j D.fits
noncomputable def sight (D:Poem C j) : Dash.Shot C.book:=⟨D.n+1,0,Fin.cons (⟨0,0⟩:C.book.Token) D.token,D.reads⟩
abbrev singer (i: V0) := valve (D.template i) C j
noncomputable def opening (D:Poem C j) :Body:= ⟨fun x=>↑((fuel D.template C j)⁻¹* D.singer 0 x), Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (D.singer 0).contDiff)⟩
noncomputable def post (i:I) : Body:= ⟨Complex.ofRealCLM ∘ (D.singer i.succ), Complex.ofRealCLM.contDiff.comp (D.singer i.succ).contDiff⟩
lemma splits (x:Points (D.n+1)): D.reads x=D.opening.val (x 0)*(∏ i:I,(D.post i).val (x i.succ)):=by
    change ↑((fuel D.template C j)⁻¹* ∏ i:V0, D.singer i (x i)) = ↑((fuel D.template C j)⁻¹* D.singer 0 (x 0))*(∏ i:I,(D.singer i.succ (x i.succ):ℂ)); push_cast; rw [Fin.prod_univ_succ,mul_assoc]
lemma opening_there : tsupport D.opening.val⊆ closedBall 0 (α! j/16):=by
   have hv: D.template 0=0:=by rw [template,points_apply,D.centered]; ext i;simp [Schedule.gridPoint]
   have hX: tsupport D.opening.val⊆ tsupport (D.singer 0):=closure_mono (fun x hx=> fun H=> hx (by change (↑(_* D.singer 0 x):ℂ)=0; rw [show D.singer 0 x=0 from H,mul_zero];rfl)); rw [(D.singer 0).tsupport_eq] at hX
   change tsupport D.opening.val⊆ closedBall (0:E4) _; rw [←hv]; exact hX
lemma tucked (i:I) : tsupport (D.post i).val⊆ closedBall (D.template i.succ) (α! j/16):=by
   let f:= D.singer i.succ; have hx: Function.support (D.post i).val ⊆ Function.support f:=fun x hx hp=> hx (by change (↑(f x):ℂ)=0; rw [show f x=0 from hp]; rfl)
   exact (closure_mono hx).trans (by rw [show closure (Function.support f)= _ from f.tsupport_eq]; exact subset_rfl) -- subset trans_eq issue
variable {T:YM.Table C.book}(hK: T.Smooth)
lemma recorded (v:C.label d) : D.sight.record v=Fin.cons ⟨d,v⟩ D.token:=by unfold Shot.record; unfold sight; simp
include hK
lemma sanctioned : Live T:= fun _ p u=> YM.Test.smearing u (T.smooth_read hK p).continuousOn -- include
omit hK in
abbrev passField (D:Poem C j)(S:YM.Table C.book)(L:S.Smooth)(d:ℕ) : S.Field d→ₗ[ℂ]ℂ:= (D.sight.core (d:=d) S (sanctioned L)).toLinearMap.comp (S.representative d)
lemma intact {h:T.Symmetric} (u:C.label d): D.passField T hK d (T.project d u)=D.sight.core T (sanctioned hK) u:=by
    let f: C.label d→ℂ:=D.sight.core T (sanctioned hK); let x:=T.representative d (T.project d u)
    have hv:x-u ∈ T.null d:= (Submodule.Quotient.mk_eq_zero _).1 (by change T.project d (x-u)=0; unfold x; rw [map_sub,T.rep,sub_self])
    have hx : D.sight.core T (sanctioned hK) (x-u)=0:= ((T.equivalent hK h _ _).mp hv) _ _ D.sight.i (show (D.sight.record (x-u) D.sight.i)=⟨d,x-u⟩ from (by simp [Shot.record])) _
    rw [map_sub, sub_eq_zero] at hx; exact hx
end Poem
-- first produce approximating tuples and pass linear price.Labeled.A
open Poem
variable (T:YM.Table C.book) (H:T.Hierarchy) (D: Contacts.Foci T d)
private def place (j:ℕ)(B:Exterior C.book):Fin (B.n+1)→ Cover:= Function.update (Extraction.address (C.S.a j) B.point) 0 0
local notation "W"=> D.index
local notation "x"=> fun i:W=> (D.shell i).point
private def node (i:W)(j:ℕ):=points (fun k=>C.S.gridPoint j (place j (D.shell i) k)) -- explicit T implied?
lemma approach (u: D.index) : Tendsto (fun j:ℕ=> node T D u j) atTop (𝓝 (x u)):=by
    let z:= (x u); let b:= D.shell u; let L:= phiL (b.n+1)
    have h : Tendsto (fun i=> L (node T D u i)) atTop (𝓝 (L z)):= ?p
    have he := (L.symm.continuous.tendsto (L z)).comp h
    rw [L.symm_apply_apply] at he; exact he.congr (fun j=> L.symm_apply_apply _)
    apply tendsto_pi_nhds.mpr; intro i; by_cases hx:i=0
    · subst i; suffices h: Tendsto (fun j:ℕ=> C.S.gridPoint j (place j b 0)) atTop (𝓝 (z 0)) from h; simp_rw [show z 0=0 from D.rooted u, place, Function.update_self,show ∀ j,C.S.gridPoint j 0=0 from fun j=>by ext i;simp [Schedule.gridPoint]]; exact tendsto_const_nhds
    let g:= fun j:ℕ=> Extraction.tag (C.S.a j) (Extraction.address (C.S.a j) z); have he:= chosen (S:=C.S) z; apply Tendsto.congr' _ (((Continuous.continuousAt (f:=fun w:Points (b.n+1)=> w i) (by fun_prop)).tendsto).comp he); exact Eventually.of_forall fun k=> by change _= C.S.gridPoint k (place k b i); unfold place; rw [Function.update_of_ne hx]; rfl
local notation "V!"=> Poem C
include H
omit H in
lemma promising (u: D.index) : ∀ᶠ j in atTop,sand (node T D u j) (C.S.a j/16)⊆conf _:=by
   filter_upwards [converging _ (D.shell u).clear (fun j=> node T D u j) (approach T D u) 0 continuousOn_const 1 one_pos] with j hj; exact hj.choose
omit H
private def emit (u:D.index) (hv:sand (node T D u j) (C.S.a j/16)⊆conf _) : Poem C j:=⟨_,(D.shell u).letter, place j (D.shell u),Function.update_self ..,hv⟩
include H
private def beam (i:W)(j:ℕ): T.Field d→ₗ[ℂ]ℂ:= if h:sand (node T D i j) (C.S.a j/16)⊆conf _ then passField (emit T D i h) T H.smooth d else 0
lemma flashed (u:D.index) (v:T.Field d): Tendsto (fun j=> (beam T H D u j) v) atTop (𝓝 (T.spectra d v (D.shell u))):=by
   rw [Metric.tendsto_nhds]; intro ε he; obtain ⟨a,rfl⟩:= T.onto _ v; let x₀:=D.shell u; let p:Fin (x₀.n+1)→C.book.Token:=Fin.cons ⟨d,a⟩ x₀.letter; let F(y):=T.read (n:=x₀.n+1) y p
   filter_upwards [converging x₀.point x₀.clear (fun j=>node T D u j) (approach T D u) F (T.smooth_read H.smooth p).continuousOn (ε/2) (half_pos he)] with i hi; obtain ⟨hp,hp'⟩:=hi; rw [beam,dif_pos hp]; let D₁:=emit T D u hp; erw [intact (h:=H.laws.toSymmetric)]; rw [dist_eq_norm]; apply lt_of_le_of_lt ?_ (half_lt_self he); change ‖D₁.sight.f.applyTo (fun z=> T.read z (D₁.sight.record a)) - F x₀.point‖ ≤_; rw [recorded]; exact hp'

lemma selected : ∀ᶠ j in atTop, ∃ Q':D.index→ Poem C j, Function.Injective (LinearMap.pi fun i:D.index=> passField (Q' i) T H.smooth d):=by
   let f : T.Field d→ₗ[ℂ] (W→ℂ):= (LinearMap.pi fun i:W=> (LinearMap.proj (D.shell i) : (Exterior C.book→ℂ)→ₗ[ℂ]ℂ).comp (T.spectra d))
   let φ (j:ℕ) : T.Field d→ₗ[ℂ] (W→ℂ):= LinearMap.pi fun i=> beam T H D i j
   have hF: Function.Injective f.toContinuousLinearMap:=by intro u v he; exact (D.detects u).symm.trans ((congr_arg (fun X: (D.index→ℂ)=> D.decoder X) he).trans (D.detects v))
   let _ := f
   filter_upwards [eventually_all.mpr (fun i=> promising T D i), (Dash.fit_plane φ f (fun i => tendsto_pi_nhds.mpr fun j=> flashed T H D j i)).eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hF)] with j h H0; refine ⟨fun i=> emit T D i (h i),?_⟩; have ht : Function.Injective (φ j):=H0; unfold φ beam at ht; simpa only [h, dif_pos] using ht
end YM.RG05Readout.Bay
