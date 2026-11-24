import YM.RegulatorIR.Gain.Craft

/-!
# Bind Grip basis and Tilt curve

Pose on both fiber legs. Need pole pre-block bill from cover and wire (K.Step
root gauges), then prove all Lean algebra diagonal links and Squad Ground. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{I J X Y Z:Type}{f c:Side}{P l u:ℝ}{m:ℕ}

-- specify $P$ & phi. pole K rows oriented correctly. Provide proof of actual joint native identities in context.

variable {A: Deck P (Foot G) (Book G f)} {B: Deck P (Foot G) (Book G c)}
variable (D:GridStep A B) (J₀:Layer (Foot G) (Foot G))(V:Bride G)

-- pole support left column (used on inputs of basis), no identity on rest

def leggy (J:Layer X Y) : Layer (X⊕Y) (X⊕Y):= Function.swap (glued 0 J 0 0)

def tubeO (K: Layer (Book G f) X) (F : Layer (OPoint G f) X)(e:OEdge f)(j:Mood G): X→ℝ:= (![ K (e,j.2), F (e.val.1,j.2), F (e.val.1+step e.val.2,j.2) ]:Fin 3→X→ℝ) j.1

def halo : Curve (Foot G) (Foot G):= fun i t=> loom (pet G i.2 t) (tubeL J₀ V i.1)

def localize : Curve (Book G f) (Book G c):= fun i t=>loom (pet G i.2 t) (tubeO (wrapL A B J₀) (scene V B) i.1)
-- A B implicit not fixed? `D` to disambiguate via type

def grain : Strip D:= { pole:= leggy J₀,space:=halo J₀ V, run:=localize (A:=A) (B:=B) J₀ V }
variable {J₀ V}
structure Passport (A:Deck P (Foot G) (Book G f))(B:Deck P (Foot G) (Book G c))(D : GridStep A B) (J₀:Layer (Foot G) (Foot G))(V:Bride G): Prop where
 sync : D.driftL= Function.swap (hoses (Gain.valve J₀ V))
 level : Layer.Sym A B J₀
 consistent : Layer.Sym A B (Gain.valve J₀ V) -- incoming from bios
 radians : Rune B f V
 costL : Billed J₀
 costH : Billed V

section Mono
-- evaluate one-element flag
lemma mono_i (T:Packet I 1)(x: I) : strum T (Pi.single x (1:ℝ): I→ℝ) = T (fun _=>x):=by
 unfold strum; let z: Tuple I 1:= fun _=>x;rw [tsum_eq_single z];simp [z,noodle]
 intro v h; have hp:v 0≠x:=fun hz=>h (funext (fun i=> by rw [Subsingleton.elim i 0]; exact hz));simp [noodle,hp,Pi.single_apply]
lemma scan_i (K:Layer I J)(i:I)(j:J):scanL K (Pi.single j 1:J→ℝ) i=K i j:=by simp [scanL,Pi.single_apply,mul_ite]
lemma cardinal (K:Layer (Mood G) X)(i:X)(a:G.ColorIndex): (loom (pet G a 0) K) (fun _=>i) = K (0,a) i + K (1,a) i-K (2,a) i:=by
 let f: Unit↪X:= ⟨fun _=>i,fun _ _ _=>rfl⟩
 have hp:dilute f (fun _=>1)=Pi.single i 1:=by
    ext1 x; by_cases he:x=i
    · subst x; rw [show i=f () from rfl,dilute_here,Pi.single_eq_same] -- rw dependency
    have hz:=dilute_miss f (fun _=>1) x (fun h=> by obtain ⟨z,H⟩:=h;exact he H.symm);simpa [Pi.single_apply,he] using hz
 let x(v:Mood G):=K v i; let P:=(lineTrip G).symm x
 rw [← mono_i (loom (pet G a 0) K),← hp,shoots, hp]
 rw [show scanL K (Pi.single i 1)= lineTrip G P from Eq.trans (funext (fun i=>scan_i K i _)) ((lineTrip G).apply_symm_apply x).symm, boots];rfl
end Mono

variable (h:Passport A B D J₀ V)
include h
lemma legend : Layer.Sym (Step.combine A B) (Step.combine A B) (leggy J₀):=by
 rintro d (i|i) (j|j) <;> first| rfl| exact h.level ..
lemma leg_v : wrapL (Step.combine A B) (Step.combine A B) (leggy J₀)=leggy (wrapL A B J₀):=by
 let p:=Step.combine A B
 let g:Layer (Foot G⊕ Foot G) (Foot G⊕Foot G):= glued 0 J₀ 0 0
 have he:Layer.Sym p p g := fun d x y=>legend D h d y x
 change fmat p p (Function.swap g)= _;rw [fmat_trans p p g he]; unfold g;rw [fmat_glue,fmat_dark,fmat_dark,fmat_dark]; rfl
lemma ocean : Gradient.diagonal (firstChannel A B).native (lastChannel A B).native D.driftL (halo J₀ V):=by
 intro i q; have hx:=cardinal (tubeL J₀ V i.1) (q 0) i.2; rw [h.sync]
 rw (occs:=.pos [1])[show q=fun _=>q 0 from funext fun p=>congr_arg q (Subsingleton.elim ..)];
 change loom _ _ _= valve _ _ _ _; rw [hx,valve];change J₀ i (q 0)+V (i.1.1,i.2) (q 0)-_= _; exact add_sub_assoc ..

lemma braked (hS:Even f.val)(hL:l*f.val=P)(HV:A=Carto G l P hS hL) : (grain D J₀ V).Ground :=by
 refine { horizontal:= legend D h,links:=ocean D h,inverted:=?_ }; subst A
 let A:=Carto G _ _ hS hL; let K:= valve J₀ V
 have hh:D.mean= lamber (fmat A B K):=by
    rw [GridStep.mean,h.sync]; change fmat (Step.combine A B) _ (Function.swap _) = _;rw [fmat_trans (Step.combine A B) _ (hoses K) (Terrain A B K h.consistent), fmat_hose];rfl
 intro i q; let T:= tubeO (wrapL A B J₀) (scene V B) i.1
 rw [hh]
 have hf:fmat A B K i (q 0)=_:= ferry hS hL h.radians h.costL h.costH rfl i (q 0)
 rw (occs:=.pos [1]) [show q=fun _=>q 0 from funext (fun j=>congr_arg q (Subsingleton.elim ..))]
 change loom _ T _= _; rw [cardinal]
 change _= fmat A B K i (q 0); rw [hf]; exact add_sub_assoc ..
end YM.RegulatorIR.Gain
