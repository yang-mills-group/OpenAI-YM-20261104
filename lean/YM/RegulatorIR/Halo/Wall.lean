import YM.RegulatorIR.Halo.Celestial

/-!
# Check source with native finite representative (gauge invariant, finite patches)

This covers physical differentiated stencil deposits if supplied by field
part. No Ward identity *after sending through the maps* assumed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}
variable {S: Heir n G}

abbrev Portrait (G:Gauge):=ℝ → CoverConfig G→ℝ
attribute [local instance] Gauge.frobInner
structure Person (B:Portrait G) : Prop where
 cap : Continuous (fun t:ℝ × CoverConfig G=>B t.1 t.2)
 guise : ∀ t,Lattice.GaugeInvariant (B t)
 neat {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (b:E→ℝ)(U:E→CoverConfig G) : (∀ i:Edge Cover,ContDiffAt ℝ ∞ (fun x:E=>G.mat (U x i)) 0)→ ContDiffAt ℝ ∞ b 0→b 0=0→ U 0=1 → ContDiffAt ℝ ∞ (fun x:E=> B (b x) (U x)) 0
-- use explicit finite-rank polynomial equality hypothesis from field dictionaries. This
-- is spacetime local symbol hypothesis, not RG transported. Generous m.

def outing (G:Gauge)(B: Portrait G)(x:Foot G→ℝ)(t:ℝ):ℝ:= B t (win G (t • x))
def shelter (m:ℕ)(T:Orders (Foot G))(x:Foot G→ℝ):= PowerSeries.mk fun e=> drums (T e) (e+m) x
structure BasisT (m s:ℕ)(B:Portrait G)(T:Orders (Foot G)):Prop where
 origin : Person B
 canopy : ∀ i r, Bounded (T i r)
 symmetry : gradedSymmetric T
 pose (v): tale (outing G B v)=PowerSeries.X^s *shelter m T v
variable {B:Portrait G}
def convey (t:Cover)(B : Portrait G) := fun (u:ℝ) (x:CoverConfig G)=> B u (translate t x)
def carryX (t:Cover): Equiv.Perm (Foot G) := (Geometry.latticeWalk G.ColorIndex 1).lamp t

lemma carrier (t:Cover)(w:Foot G→ℝ): translate t (win G w)=win G (w ∘ carryX t):=by
 ext1 i; unfold translate win;rw [add_comm]; rfl
lemma Person.vayne (P: Person B)(t: Cover) : Person (convey t B):=by
 refine ⟨?_,?_,?_⟩
 · let f (p:ℝ×CoverConfig G):= (p.1,translate t p.2); apply P.cap.comp (f:=f); unfold f translate; fun_prop
 · intro a f U; unfold convey; rw [show translate t (Lattice.gauge f U)=Lattice.gauge (fun j=>f (j+t)) (translate t U) from ?_]; apply P.guise a
   ext1 i; simp [translate, Lattice.gauge,add_right_comm]
 intro E _ _ b U h hs hb hu; refine P.neat b (fun x=>translate t (U x)) (fun _=> h _) hs hb ?_; rw [hu];rfl

lemma echoed {r:ℕ}{T:Packet (Foot G) r}(h:Bounded T) (A:Equiv.Perm (Foot G)): Bounded (echo A T):=by
 let F: Equiv.Perm (Tuple (Foot G) r):= Equiv.piCongrRight (fun _=>A.symm)
 apply Set.Finite.preimage (f:=F) ?_ h
 exact F.injective.injOn
lemma strums {r:ℕ}(T:Packet (Foot G) r)(A:Equiv.Perm (Foot G))(w: Foot G→ℝ): strum (echo A T) w=strum T (w ∘ A):=by
 rw [strum_perm w A]
 have hh : (fun z:Tuple (Foot G) r=>echo A T (A ∘ z))=T:= funext (echos A T)
 rw [hh]
lemma BasisT.vayne {m s:ℕ}{F:Orders (Foot G)} (R:BasisT m s B F)(t:Cover) : BasisT m s (convey t B) (fun e r=> echo (carryX t) (F e r)):=by
 refine ⟨R.origin.vayne _,fun i r=>echoed (R.canopy i r) _,fun i r=> echo_sym (R.symmetry i r),?_⟩
 intro x; rw [show outing G (convey t B) x=outing G B (x ∘ carryX t) from funext fun u=> congr_arg (B u) (carrier ..), R.pose]; apply congr_arg; ext1 i; rw [shelter,shelter,coeff_mk,coeff_mk];unfold drums; simp_rw [strums]

variable {f:Side}
def vital (f:Side) (B:Portrait G): Hook G Empty (OEdge f) := fun t u _=> B t (orbLift u ∘ around f)
lemma gifted (f:Side) (P:Person B) : Plan G f (vital f B):=by
 refine ⟨?_,?_,?_⟩
 · intro k hk U t; unfold vital; dsimp only; rw [goat_lift k U hk];
   have hp: Lattice.gauge k (orbLift U) ∘ around f = Lattice.gauge (k∘ wrap f) (orbLift U ∘ around f):=by
      ext1 x; simp [around, Lattice.gauge]
   rw [hp]; exact P.guise ..
 · let X (v:ℝ × RoomK G (OEdge f) × RoomK G Empty): ℝ×CoverConfig G:= (v.1, orbLift v.2.1 ∘ around f)
   exact P.cap.comp (f:=X) (continuous_fst.prodMk (continuous_pi (fun i=> (continuous_apply (around f i)).comp ((lift_cont _).comp (continuous_fst.comp continuous_snd)))))
 let X:=(Angle Empty (OEdge f) G); let b(x:X):= x.2.1; let F(x:X):=orbLift (climb x.2.2) ∘ around f
 refine P.neat b F (fun i=> ?_) (contDiffAt_fst.comp (f:=Prod.snd) _ contDiffAt_snd) rfl ?_
 · let t:= around f i; change ContDiffAt ℝ ∞ (fun x:X=>G.mat (orbLift (climb x.2.2) t)) 0
   let x':X:=0; let g(x:X):=x.2.2 (index t); have hp:ContDiffAt ℝ ω g 0:= (contDiff_apply ℝ G.Color _).contDiffAt.comp _ (contDiffAt_snd.comp (f:=Prod.snd) (0:X) contDiffAt_snd)
   have hh:= G.exp_jet.contDiffAt.comp (f:=g) x' hp -- check
   unfold orbLift liftLinks;split_ifs <;> first|exact hh.of_le le_top| (simp_rw [mat_inv]; exact ((starL' ℝ).contDiff.contDiffAt.comp _ hh).of_le le_top)
 change orbLift (Binding.climb (0:Horizon G f)) ∘ around f=1; rw [show Binding.climb _= (1:spins G f) from expOrigin .., Geometry.lift_one];rfl
variable {m s:ℕ} {l u P:ℝ}
lemma script {T: Orders (Foot G)}(X:BasisT m s B T) (H:Even f.val)(hv:l*f.val=P)(y:Horizon G f):
 let A:=Carto G l P H hv; PowerSeries.X^s*flavor m (tint G f y) (fun i r=> A.scroll (T i r))= inscription (priceMap (vital f B)) (0,1,y):=by
 intro A; rw [← lore (gifted f X.origin).tune.smooth]
 let v:=bridge A (paper G f y)
 rw [show (fun t:ℝ=>priceMap _ _)=outing G B v from ?_,X.pose];
 · apply congr_arg; ext1 i; rw [flavor_lo,shelter,coeff_mk]; exact high_ink (paper G f y) A _ (X.canopy i)
 ext1 t; rw [priceMap,vital]; change B (t*1) _=_; rw [mul_one];
 have hv' : bridge A (paper G f (t • y))=t • v:=by
    ext1 i; rw [map_smul]; change _*(t*_)= t*(_*_);ring
 unfold outing; rw [← hv', win_o];rfl
lemma grade_s {T: Orders (Foot G)}(X:BasisT m s B T) (H:Even f.val)(hv:l*f.val=P):let A:= Carto G l P H hv; gradedSymmetric (fun i r=> A.scroll (T i r)):=by
 intro A i r p z; dsimp only; rw [← show A.scroll (T i r ∘ Tuple.perm _ p) z=A.scroll (T i r) (z∘ p) from A.scroll_perm _ p z]; exact congr_arg (fun v:Packet _ r=>A.scroll v z) (funext (X.symmetry i r p))
section Hist
variable (H:Reel S)(T:S.Accounts)(J:T.Report m)(HH:H.Follows T)(V : W→Portrait G)
variable (hc : ∀ w,BasisT m s (V w) (J.main (Page.opening M w)))
include HH hc
lemma hinted : Coverage T J H.docket (fun w=> vital (TopF n w) (V w)) s:=by
 refine ⟨fun w=>gifted _ (hc w).origin,fun w=>?_⟩
 let i:= Page.opening M w; let f:= n i
 have hz := H.accorded T HH w
 refine ⟨hz.1,fun p=>?_,T.top_o _, hz.2, J.ceilingP w,?_⟩
 · rw [show J.point i=fun e r=> (S.maps i).scroll (J.main i e r) from funext fun _=> funext fun _=> J.same w _ _, H.realms];exact script (hc w) (H.even i) (H.phase i) p
 rw [show J.point i=fun e r=> (S.maps i).scroll (J.main i e r) from funext fun _=> funext fun _=> J.same w _ _, H.realms]; exact grade_s (hc w) (H.even i) (H.phase i)

variable (w:W)
def frame_loc (z:Side): Cover:= (n (Page.opening M w)).val • journey z
lemma curry_top (z:Side): let p:=Page.opening (extent M w) z; BasisT m s (convey (frame_loc w (n:=n) z) (V w)) ((gazer H T J w HH).main p):=by
 intro p; let i:=Page.opening M w
 change BasisT _ _ _ (fun a b=> echo _ (J.main i a b))
 have hy: shiftE (S:=S) w (p)=carryX (frame_loc w (n:=n) z):=by unfold shiftE;rw [H.realms];ext1 k; rfl
 rw [hy];exact (hc w).vayne _
variable (hr:Common H)
include hr
lemma glowing (p:Page (extent M w)): let E:= grove H w hr; let v:= p.bindW;let i:= Page.opening (extent M w) v; let f:=big w n i; let A:=tele H T w; let T':= gazer H T J w HH; let S':= convey (frame_loc w (n:=n) v) (V w); Nonempty (RangeR G (big w n p) (E.spot p) (goal (E.clock i) (vital f S')) s m (A.orb p) (T'.point p)):=by
 intro E v i f A T' S'; let g(z:Side):=convey (frame_loc w (n:=n) z) (V w)
 have hx:= hinted E A T' (knows H T w hr HH) g (curry_top H T J HH V hc w); exact Coverage.craved A T' E.docket _ hx p
end Hist
end YM.RegulatorIR.Halo
