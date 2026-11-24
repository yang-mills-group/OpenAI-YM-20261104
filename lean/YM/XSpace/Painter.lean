import YM.XSpace.Opal
/-!
# Painted values for §tri (explicit local-chart convention)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Set Filter MeasureTheory Relief Trace Litter Tide Sail Octave Chiral Playpen Further.FreeCovariance.KP Lattice
open Maxwell (Green grad)
open scoped Topology BigOperators ContDiff RealInnerProductSpace
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v w:E4} {A B C:Toe} {k:ℕ}
def coast (i:Axis): Breeze:= -(grad i Green)
def line (σ:Bool)(p:P)(i:Axis):Breeze:= ∑ a:Axis,q σ p a i • coast a
abbrev hatch (σ τ:Bool)(p r:P)(a b:Axis):=folds σ τ p r a b
abbrev surfT (σ τ:Bool)(p r:P):Breeze:=∑ i:Axis,∑ j:Axis,hatch σ τ p r i j • grad i (coast j)
lemma fin_beam {T:Type*}(X:T→Toe)(F:T→Breeze)(s:Finset T)(h:∀ i∈s,Beam k (X i) (F i)): Beam k (∑ i∈s,X i) (∑ i∈s,F i):= by
  classical induction s using Finset.induction_on with | empty=> simpa using (Beam.zero (k:=k) (F:=ℝ)) | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
lemma coasted (i:Axis): Beam 3 (η i Sail.cover) (coast i):=by
  unfold coast; rw [down_phase]; have he:=(((greenBeam.step_forth i).moved (-step i)).smul (-1))
  rw [neg_one_smul,neg_one_smul] at he; exact he
lemma shore (σ:Bool)(p:P)(i:Axis): Beam 3 (field σ p i) (line σ p i):= by unfold field line; exact fin_beam _ _ _ fun i hi=> (coasted i).smul _
lemma charted (σ τ:Bool)(p r:P): Beam 4 (magnetic σ τ p r) (surfT σ τ p r):=by rw [magnetism]; exact fin_beam _ _ _ fun i _=> fin_beam _ _ _ fun j _=> ((coasted j).step_forth i).smul _
lemma coast_at (hx:u≠0)(i j:Axis): grad i (coast j) u= -(grad i (grad j Green) u):=by unfold coast; change fderiv ℝ _ _ _ = -(fderiv ℝ _ _ _); rw [fderiv_neg];rfl
lemma coast_even₀ (hx:u≠0)(i j): grad i (coast j) (-u)= grad i (coast j) u:=by rw [coast_at hx,coast_at (neg_ne_zero.mpr hx), Maxwell.second_Green hx,Maxwell.second_Green (neg_ne_zero.mpr hx)]; simp
lemma hes (σ τ:Bool)(p r:P)(hx:u≠0): surfT σ τ p r (-u)= surfT σ τ p r u:=by simp only [surfT,Finset.sum_apply,Pi.smul_apply,coast_even₀ hx]
lemma hesSym (σ τ:Bool)(p r:P)(hx:u≠0): surfT σ τ p r u= surfT τ σ r p u:=by
  simp only [surfT,Finset.sum_apply,Pi.smul_apply]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; congr 1; · exact Finset.sum_congr rfl fun i _=> mul_comm ..
  simp only [coast_at hx]; rw [Maxwell.Hess_sym hx i j]
-- canonical limit (metric scale Stage)
abbrev pier (u:E4)(i:ℝ):= mark i u
lemma voyage (u:E4): distance dawn id (pier u) u:= marks u starts.zero starts.good
lemma reroute (r:ℝ)(hr:0<r)(s:Stage L a): Stage L (fun i=> r*a i):=⟨by simpa using s.zero.const_mul r, s.good.mono fun i hi=> mul_pos hr hi⟩
lemma together (r:ℝ)(p:distance L a x u): distance L (fun i=>r*a i) x (r • u):= (p.const_smul r).congr fun i=> (mul_smul ..).symm
lemma share_hom (r:ℝ)(hr:0<r){f:Breeze}(p:Beam k A f)(h:u≠0): f (r • u)=r⁻¹^k* f u:= by
  have hh:= shines (reroute r hr starts) (together r (voyage u)) (smul_ne_zero hr.ne' h) p; exact tendsto_nhds_unique hh (((shines starts (voyage u) h p).const_mul (r⁻¹^k)).congr fun i=> by rw [mul_inv_rev,mul_pow]; ring)
lemma surfD (σ τ:Bool)(p r:P): magnetic σ τ p r∈ Surface 3:=by rw [magnetism]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=>Submodule.smul_mem _ _ (surface (coasted j).glows i)
-- equivalent explicit scaled numeric formula near or at any stage. `P{}_i*` acts as a derivative at w of z anchored potential, hence there use sector `moving`.
variable {g h:Breeze}(c:Shade.Cut)
abbrev parts (σ τ:Bool)(p r:P) (g h:Breeze)(u v b:E4):ℝ:=∑ i:Axis,∑ j:Axis,hatch σ τ p r i j * moving c i u v b (coast j) g h
abbrev fareT (g h:Breeze)(u v b:E4):Prop:=∀ i j:Axis, Pays₃ c i u v b (coast j) g h
lemma trail_fin {T:Type*}(p:T→Toe)(q:Finset T)(H:∀ i∈q,p i∈Terrain 4)(hy:B∈ Terrain 3)(hz:C∈ Terrain 3)(x y z:Cover): Trail x y z (∑ i∈q,p i) B C=∑ i∈q,Trail x y z (p i) B C:=by
  classical induction q using Finset.induction_on with | empty=> simp [Trail,Form] | insert i q hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi]; have hh:=fun x hx=> H x (Finset.mem_insert_of_mem hx); rw [trail_add (H _ (Finset.mem_insert_self ..)) (Submodule.sum_mem _ hh) hy hz (by norm_num),ih hh]
lemma spectral (σ τ:Bool)(p r:P)(hy:B∈ Terrain 3)(hz:C∈ Terrain 3)(x y z:Cover): Trail x y z (magnetic σ τ p r) B C=∑ i:Axis,∑ j:Axis,hatch σ τ p r i j*Trail x y z (D i (η j Sail.cover)) B C:=by
  let f (i j:Axis):=folds σ τ p r i j • D i (η j Sail.cover); have he(i j:Axis):f i j∈Terrain 4:= Submodule.smul_mem _ _ (steps_hill (down_hill hill2 j) i)
  rw [magnetism,trail_fin _ _ (fun i _=> Submodule.sum_mem _ fun j _=> he i j) hy hz]; apply Finset.sum_congr rfl; intro i _; rw [trail_fin _ _ (fun j _=> he i j) hy hz]; exact Finset.sum_congr rfl fun j hj=> trail_smul ..
structure Gleam (c:Shade.Cut)(u v b:E4):Prop where
  uv: range c u v
  ub: range c u b
  vb: range c v b
variable (s: Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z w) (R:Gleam c u v w)(H:Beam 3 B g)(K:Beam 3 C h) (σ τ: Bool)(p r:P)
include s X Y Z R H K in
lemma preps [L.IsCountablyGenerated][NeBot L]: Tendsto (fun i=> (a i)⁻¹^6*Trail (x i) (y i) (z i) (magnetic σ τ p r) B C) L (𝓝 (parts c σ τ p r g h u v w)):=by
  simp_rw [spectral _ _ _ _ (show B∈Terrain 3 from H.glows) (show C∈Terrain 3 from K.glows), Finset.mul_sum]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _ => (((lights c i s X Y Z R.uv R.ub R.vb (coasted j) H K).2).const_mul _).congr fun u=>mul_left_comm ..))
include R H K in
lemma prep : fareT c g h u v w:=fun i j=> (lights c i starts (voyage u) (voyage v) (voyage w) R.uv R.ub R.vb (coasted j) H K).1
include R H K in
lemma same_fare (d:Shade.Cut)(T:Gleam d u v w): parts c σ τ p r g h u v w=parts d σ τ p r g h u v w:= tendsto_nhds_unique (preps c starts (voyage u) (voyage v) (voyage w) R H K σ τ p r) (preps d starts (voyage u) (voyage v) (voyage w) T H K σ τ p r)
include R H K in
lemma swept (d:Shade.Cut)(x:ℝ)(hx:0<x)(T:Gleam d (x • u) (x • v) (x • w)):parts d σ τ p r g h (x • u) (x • v) (x • w)=x⁻¹^6 * parts c σ τ p r g h u v w:=by
  have hh:= (preps c starts (voyage u) (voyage v) (voyage w) R H K σ τ p r).const_mul (x⁻¹^6); refine tendsto_nhds_unique (preps d (reroute x hx starts) (together x (voyage u)) (together x (voyage v)) (together x (voyage w)) T H K σ τ p r) (hh.congr fun i=>?_); rw [mul_inv_rev,mul_pow]; ring
end YM.XSpace.Season
