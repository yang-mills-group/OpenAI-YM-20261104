import YM.RegulatorIR.Gain.Mirage

/-!
# Hide a growing inner sampling sheet in shifted replica orbit

Recover compact-test arguments and arbitrary uniformly bounded cover forms
via signal limit. Both sites and edges, including escaping from origin and
all other fixed points modulo theta. Site preimages allowed to share global
root. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I J:Type}{u i p:ℕ} (f z : Side)
abbrev rep (f z:Side): Side:= Sight.slab z*f
abbrev fromZ (f:Side)(z:Side):= f.val • journey z
def inside (z:Side)(x:Cover):Prop:= x∈ Lattice.box z.val
lemma included (x:Cover): ∀ᶠ z: Side in atTop,inside z x:=by
 let B:= Finset.univ.sup fun i:Axis=> (x i).natAbs; let v:Side:=⟨B+1,by omega⟩
 filter_upwards [eventually_ge_atTop v] with z hz; change B+1≤ z.val at hz
 have he i : (x i).natAbs≤z.val:= le_trans (Finset.le_sup (s:=Finset.univ) (f:=fun i: Axis=>(x i).natAbs) (Finset.mem_univ i)) (show Finset.univ.sup (fun i=> (x i).natAbs) ≤ z.val from by omega)
 exact Lattice.box_test.mpr ⟨fun i=>by specialize he i; omega,fun i=>by specialize he i;omega⟩

def swim (x:Cover):= wrap (rep f z) (fromZ f z+x)
def deep (i : Edge Cover):= dis (fromZ f z) i

section Raise
variable {f z} (h:4 ≤ f.val){x y:Cover}{e t:Edge Cover}
private lemma crude {x:Cover}(H:inside z x) (i:Axis): -((z.val:ℕ):ℤ)≤ x i ∧ x i≤ z.val := ⟨(Lattice.box_test.mp H).1 i, (Lattice.box_test.mp H).2 i⟩
include h in
private lemma seat {x:Cover}(H:inside z x)(i:Axis): let u:= fromZ f z+x; -((rep f z).val:ℤ)<2*(u i-1) ∧ 2*(u i+1)< (rep f z).val:=by
 intro u;obtain ⟨hg,hh⟩:= crude H i; have hv : (4:ℤ) ≤ f.val:=by exact_mod_cast h
 have hz : (1:ℤ)≤ z.val:=by exact_mod_cast z.property
 unfold rep Sight.slab; simp only [PNat.mul_coe, Nat.cast_mul]; change - (4*(z.val:ℤ)*f.val)< _ ∧ _< 4*(z.val:ℤ)*f.val -- check constants cast
 unfold u fromZ Halo.journey; simp only [Pi.add_apply, Pi.smul_apply,step_apply];split <;> simp only [nsmul_eq_mul, mul_one,mul_zero,zero_add] <;> constructor <;> nlinarith
include h
lemma seated {x:Cover}(H:inside z x): Lattice.lift (swim f z x)=fromZ f z+x:=by
 refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩
 have hh:=seat h H i;dsimp only at hh; omega
lemma seated_m {x:Cover}(H:inside z x): Lattice.lift (-swim f z x)= -(fromZ f z+x):=by
 refine lift_eq_iff.mpr ⟨Eq.symm (map_neg ..),fun i=>?_⟩
 rw [Pi.neg_apply]; have hh:=seat h H i;dsimp only at hh;omega
lemma seated_w {x:Cover}(H:inside z x)(v: Axis): Lattice.lift (-swim f z x - Lattice.step v)= -(fromZ f z+x)-Lattice.step v:=by
 refine lift_eq_iff.mpr ⟨?_,fun i=>?_⟩
 · rw [swim,map_sub,map_neg,wrap_step]
 rw [Pi.sub_apply,Pi.neg_apply, Lattice.step_apply];have hh:=seat h H i;dsimp only at hh; split <;> omega
lemma south {x: Cover} (H:inside z x) : 0<(fromZ f z+x) 0:=by
 obtain ⟨hx,hp⟩:= crude H 0; have hv:(4:ℤ)≤ f.val:=by exact_mod_cast h
 simp [fromZ, Halo.journey]; nlinarith [show 0<(z.val:ℤ) from by exact_mod_cast z.property]
lemma swim_eq (hx:inside z x)(hy:inside z y)(he:swim f z x=swim f z y): x=y:=by
 have h:= congr_arg Lattice.lift he; rw [seated (by assumption) hx,seated (by assumption) hy] at h;exact add_left_cancel h
lemma swim_ne (hx:inside z x)(hy:inside z y): swim f z x ≠ -swim f z y:=by
 intro he; have hh:= congr_arg Lattice.lift he; rw [seated h hx,seated_m h hy] at hh; have hp:=south h hx; rw [hh,Pi.neg_apply] at hp; linarith [south h hy]
lemma vertex_at (hx:inside z x)(hy:inside z y)(he: Orb.vertex (swim f z x)=Orb.vertex (swim f z y)):x=y:=by
 rcases vertex_spec (swim f z x) with hk|hk <;> rcases vertex_spec (swim f z y) with ht|ht <;> rw [hk,ht] at he <;> first| exact swim_eq h hx hy he | exact swim_eq h hx hy (neg_inj.mp he)| exact (swim_ne h hx hy he).elim | exact (swim_ne h hy hx he.symm).elim
lemma edged (hx:inside z e.1)(hy:inside z t.1)(he:resolve (rep f z) (deep f z e)=resolve _ (deep f z t)): e=t :=by
 rcases (tandem ..).mp he with hh|hh
 · refine Prod.ext ?_ (congr_arg (Prod.snd: Edge (Site (rep f z))→_) hh)
   exact swim_eq h hx hy (congr_arg Prod.fst hh)
 have he: swim f z e.1= -(swim f z t.1)-Lattice.step t.2:= congr_arg Prod.fst hh
 have hh:= congr_arg Lattice.lift he;rw [seated h hx,seated_w h hy] at hh
 have hp:=south h hx; rw [hh,Pi.sub_apply,Pi.neg_apply] at hp; exfalso; have hz:= Lattice.step_apply t.2 (0:Axis) (S:=ℤ); rw [hz] at hp; split at hp <;> linarith [south h hy]
end Raise

section Lift
variable {f} (h:4 ≤ f.val)

def slotE : {x:Edge Cover // inside z x.1}↪ OEdge (rep f z) := ⟨fun x=> resolve _ (deep f z x.val),fun a b he=> Subtype.ext (edged h a.property b.property he)⟩
def slotS : {x:Cover // inside z x}↪ Site (rep f z) := ⟨fun x=>vertex (swim f z x.val), fun a b he=>Subtype.ext (vertex_at h a.property b.property he)⟩

-- use certified generator assignment on fine edges respecting site inversion and sign

def dropV (σ:Cover→ G.Color): Site (rep f z)→ G.Color:=fun i=>Function.extend (slotS z h) (fun x=>σ x.val) (fun _=>0) (vertex i)
lemma dropV_eq (σ:Cover→ G.Color) (i:Cover)(he:inside z i): dropV z h σ (swim f z i)=σ i:= Embedding.injective (slotS z h) |>.extend_apply (fun x=>σ x.val) (fun _=>0) ⟨i,he⟩
lemma dropV_tag (σ :Cover→ G.Color): EvenSite (dropV z h σ) :=by intro i; unfold dropV; rw [vertex_neg]
private lemma reserve {f :I→J}{q:I→G.Color}{C:ℝ}(H:Injective f)(hc: 0≤C)(h:∀ i, ‖q i‖≤C)(i:J): ‖Function.extend f q (fun _=>0) i‖≤C:=by
 by_cases ht:i∈Set.range f
 · obtain ⟨b,rfl⟩:=ht;rw [H.extend_apply];exact h b
 rw [Function.extend_apply' _ _ _ ht, norm_zero];exact hc
lemma drop_bill (σ : Cover→ G.Color) {C:ℝ}(hc : 0≤ C) (hk:∀ i,‖σ i‖≤C)(j) : ‖dropV z h σ j‖≤C:= reserve (slotS z h).injective hc (fun i=> hk i.val) _

def camp (A:Edge Cover→ G.Color) (i:Edge Cover):= if Orb.eR (around (rep f z) (deep f z i))= around _ (deep f z i) then A i else -A i
def track (A:Edge Cover→G.Color) : Horizon G (rep f z):= Function.extend (slotE z h) (fun x=>camp (f:=f) z A x.val) (fun _=>0)
lemma track_bill (A:Edge Cover→ G.Color) {C:ℝ}(hc:0≤C)(hk:∀ x, ‖A x‖≤C)(u) : ‖track z h A u‖ ≤ C:= reserve (slotE z h).injective hc (fun x=> by unfold camp; split <;> simpa using hk _) _
lemma track_link (A:Edge Cover→ G.Color)(i:Edge Cover)(he:inside z i.1): fire (track z h A) (around _ (deep f z i)) = A i:=by
 let g:=slotE z h; let p:=track z h A; let w : {x:Edge Cover // inside z x.1}:=⟨i,he⟩
 have hx : p (g w)=camp (f:=f) z A i:= g.injective.extend_apply _ _ w
 unfold fire; rw [show track z h A (index _)=_ from hx]; unfold camp; split_ifs <;> simp
end Lift
end YM.RegulatorIR.Gain
