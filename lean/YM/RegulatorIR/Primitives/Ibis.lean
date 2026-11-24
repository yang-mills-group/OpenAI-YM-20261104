import YM.RegulatorIR.Primitives.Firn

/-!
# Top cover stencil root
No comparing different periods' roots directly; prove orbit restriction by
summing projected stencil. Docket top released. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Chart Gauge RG Orb Laplace
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I J X:Type}{k a b:ℕ}{f c:Side}{l P:ℝ} {G:Gauge}

-- periodic & angle
lemma polar_dir {R:Type}[AddCommGroup R][One R](p:Face R) (t:Four R) : Face.send invS t p= plateTrans t (ice p):=by
 rcases p with ⟨v,⟨⟨x,y⟩,h⟩⟩;change x<y at h
 refine Prod.ext ?_ (Subtype.ext ?_)
 · unfold Face.send ice plateTrans Face.lower; dsimp only [atFace,affine];rw [pivot_dir]
   change -v+t+ -step x + -step y= _;abel
 simp [Face.send, invS,PlaqAxes.rotate,PlaqAxes.ordered, h.le,plateTrans,ice]
lemma summer_dir {R:Type}[AddCommGroup R][One R](p:Face R)(t : Four R): Face.send 1 t p=plateTrans t p:=by
 rcases p with ⟨x,⟨⟨v,w⟩,h⟩⟩;change v<w at h; refine Prod.ext ?_ (Subtype.ext ?_)
 · simp [Face.send,Face.lower,plateTrans,affine,atFace,posDir, add_comm]
 simp [Face.send,PlaqAxes.rotate,PlaqAxes.ordered,h.le,plateTrans]
lemma incline (H:Even f.val)(d:Motion)(p) : (gliders H).rips d p= Face.send (parity d) (baseR f d) p:=by
 change windF _ _ _=_;cases d; exact (summer_dir ..).symm; exact (polar_dir ..).symm
lemma flameO (H:Even f.val) (U: spins G f)(p:Face (Per f)) : G.price (faceValue (orbLift U) (ice p))= G.price (faceValue (orbLift U) p):=by
 let Q:=orbLift U; have hp:pull invS 0 Q=Q:=by ext1 i;rw [spun, show Q (reflect i)=(Q i)⁻¹ from lift_flip H ..,inv_inv]
 have he:= Face.send_price Q p invS 0 G.price G.price_inv fun x g=>G.price_conj ..; rw [polar_dir, show plateTrans 0 (ice p)=ice p from (by simp [plateTrans]), hp] at he; exact he.symm
-- actual volume top identity. core cost per independently selected orbit positive face.

def plain (S:Scale)(G:Gauge)(p: Face ℤ):Micro (Foot G):= fun t v=> S.beta t* G.price (faceValue (win G v) p)
lemma plain_off (S:Scale)(H:Even f.val)(hz:l*f.val=P) : Offset (Carto G l P H hz) (gliders H) (plain S G):=by
 intro d x t w; unfold plain
 let φ:= win G (toolP (Carto G l P H hz) d w)
 have h:=Face.send_price φ x (parity d) (baseR f d) G.price G.price_inv fun k g=> G.price_conj ..; rw [show pull (parity d) (baseR f d) φ= _ from tools_links H hz d w,← incline H] at h
 rw [h]
lemma plain_rest (S:Scale)(G:Gauge)(p) s : plain S G p s 0=0:=by unfold plain win; rw [timber_0]; simp only [Pi.zero_apply, G.mat_lieExp_zero]; rw [faceValue, show travel _ _ _= (1:G.El) from ?_, G.price_one,mul_zero]; generalize square _ _=w; generalize p.1=x; induction w generalizing x <;> simp_all [travel,Lattice.Step.read]

variable (S:Scale) (G)
attribute [local instance] Gauge.frobInner
-- analytic chart proof on finite restriction
lemma normWalk {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (U:E→CoverConfig G)(h:∀ i,ContDiffAt ℝ ω (fun p:E=>G.mat (U p i)) 0) b w: ContDiffAt ℝ ω (fun p:E=>G.mat (travel (U p) b w)) 0 := by
 induction w generalizing b with
 | nil => exact contDiffAt_const
 | cons a w ih =>
    simp only [travel,G.mat_mul]; apply ContDiffAt.mul _ (ih _); unfold Lattice.Step.read;split <;> first| exact h _| (simp_rw [G.mat_inv]; exact (starL' ℝ).contDiff.contDiffAt.comp _ (h _))

def basin (p:Face ℤ) : Finset (Foot G):= steps p.1 (square p.2.val.1 p.2.val.2) ×ˢ Finset.univ
lemma boons (p:Face ℤ): Nonempty (Run (plain S G p)):=by
 let u:=basin G p; let L (w:ℝ× (↥u→ℝ)):= plain S G p w.1 (fill (placeFin u) w.2)
 refine ⟨{ J:= ↥u, fin:=inferInstance, inc:=placeFin u, script:=L, smooth:=?_, reaches:=?_ }⟩
 · apply ContDiffAt.mul (S.near.comp (f:=Prod.fst) (0:ℝ× (↥u→ℝ)) contDiffAt_fst)
   apply ContDiffAt.of_le (m:=∞) (n:=ω) _ le_top; apply Work.F03.price_smooth; apply normWalk
   intro i; unfold win; exact G.exp_jet.contDiffAt.comp _ (((tall u i)|>.contDiffAt).comp (f:=Prod.snd) (0:ℝ× (↥u→ℝ)) contDiffAt_snd)
 intro t x; unfold L plain;dsimp only; apply congr_arg (fun z:G.El=> S.beta t * G.price z);apply travel_knows;intro i hi
 apply congr_arg G.lieExp; ext1 j; exact (fill_eq u (i,j) (Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩) x).symm

variable {G} (H:Even f.val)(hz:l*f.val=P)
lemma accessO (p:PFace f)(x:Horizon G f) (t): plain S G (reachF p) t (bridge (Carto G l P H hz) (paper G f x))= S.beta t*G.price (faceValue (orbLift (climb x)) p.val):=by
 unfold plain; rw [win_o H hz]; apply congr_arg (fun z=>S.beta t*G.price z); change travel _ _ _= _ 
 have hv : orbLift (climb x) ∘ around f=expandAt 0 (orbLift (climb x)):=by ext1 i; simp [expandAt, around]
 rw [hv, travel_at,add_zero,show wrap f (reachF p).1= p.val.1 from congr_arg Prod.fst (floorP p)];rfl

lemma priceStart (x:Horizon G f) :
 let z : Meadow G Empty × ℝ × Horizon G f:=(0,1,x); inscription (priceMap (startO S)) z= ∑ u:PFace f,tale (flank (plain S G (reachF u)) (bridge (Carto G l P H hz) (paper G f x))):=by
 intro z; let W(u:PFace f):=flank (plain S G (reachF u)) (bridge (Carto G l P H hz) (paper G f x));rw [← lore (startF S).smooth]
 have hp (u:PFace f): ContDiffAt ℝ ∞ (W u) 0:= (boons G S (reachF u)).some.smooth_v _
 change _=∑ i,tale (W i); rw [← tale_sum (s:=Finset.univ) W (fun i _=>hp i)];apply congr_arg; ext1 t
 rw [Finset.sum_apply]
 have hh (u:PFace _): W u t= S.beta t*G.price (faceValue (orbLift (climb (t • x))) u.val):=by
    unfold W flank; rw [show t • bridge _ _=bridge (Carto G l P H hz) (paper G _ (t • x)) from ?_]; exact accessO S H hz u (t • x) t
    ext1 i; rw [map_smul]; change t*(_*_)= _*(t*_); ring
 change S.beta (t*1)* valueO (climb (t • x))= _; rw [mul_one]; unfold valueO Wilson.energy; rw [plate_both H _ (flameO H _)]; simp_rw [hh]; rw [← Finset.mul_sum];ring

-- Without assuming equality on quotient. Positive inputs all powers.
abbrev Plane (S:Scale)(G:Gauge)(T:Face ℤ→ Orders (Foot G)):= ∀ p, Lab 2 (-1) (plain S G p) (T p)
lemma plain_exists (S:Scale)(G:Gauge):∃ T, Plane S G T:=by choose T h using fun p=> (boons G S p).some.issues (-1) 2; exact ⟨T,h⟩
variable {T:Face ℤ→ Orders (Foot G)}
lemma ark (h:Plane S G T) : Flight (plain S G) T (fun _=>2) (fun _=>-1) (Carto G l P H hz) (gliders H):=⟨plain_off S H hz,h,fun _=>le_rfl, fun _ _=>rfl,fun _ _=>rfl,plain_rest S G⟩
abbrev Iris (H:Even f.val)(hz:l*f.val=P)(T:Face ℤ→Orders (Foot G)):= Flight.foldO (Carto G l P H hz) T
-- Canvas.logA from massive
lemma log_eye (h:Plane S G T)(x:Horizon G f) : flavor 2 (paper G f x) (Iris H hz T)= logread (priceMap (startO S)) (0,1,x):=by
 let V:=ark S H hz h
 ext i
 unfold Iris; cases Nat.eq_zero_or_pos i with
 | inl hi=> rw [hi,V.zero_transit,logbase]
 | inr hi=>
    let z: Meadow G Empty × ℝ × Horizon G f:=(0,1,x); let T:=tale; rw [Flight.transit V _ hi, logread, PowerSeries.coeff_mk, Series.Radial.layers,if_neg hi.ne',add_zero, show jet (priceMap (startO S)) (i+2) (0,1,x)=PowerSeries.coeff (i+2) (inscription (priceMap (startO S)) z) from (by rw [inscription, PowerSeries.coeff_mk])]
    change (∑ v:PFace f, (-1:ℝ)*_)= -PowerSeries.coeff (i+2) (inscription (priceMap (startO S)) z); rw [priceStart S H hz x,map_sum,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl;intro v _; rw [neg_one_mul]; rfl
end YM.RegulatorIR.Prim
