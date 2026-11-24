import YM.FVA2.MatrixTime
/-!
# Panel. Real operator actions on physical sector actual point kernels.

Here using all separated points.That view is equivalent to tested profile (all smooth
joint tests) once continuity established. Don't invent near-corner assumptions. Need graded
MS projection. `Ready` used for polynomial property.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.FVA2
open Function Filter Set MeasureTheory Pert Pert.Position Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector Elegant PayAll WorldJet Verne Strat ColorCode MS.Book MS.Book.Convolve PowerSeries Clock Attend
open scoped Topology ContDiff Classical
variable {G:Gauge}{F:Labels.Frames G} {m n d e k:ℕ}
abbrev Polyp (m:ℕ):= ↥(conf m)
structure Panel (F:Labels.Frames G) where
    out (d:ℕ){m:ℕ}(x:Polyp m): PayAll.reprK F d m
namespace Panel
variable (A B:Panel F)(T: Strat F)(φ: Word ℝ)
variable (f:PayAll.reprK F d m) (p: Test m) (w: Fin m→ E F d)(x: Polyp m)
-- interpolate.Removing back of points where profile zero.
def off (A:Panel F)(d:ℕ){m:ℕ}(x:Points m) : PayAll.reprK F d m:= if h:x∈ conf m then A.out d ⟨x,h⟩ else 0
lemma sees (A:Panel F) {x:Points m} (hx:x∈conf m): A.off d x=A.out d ⟨x,hx⟩:= dif_pos hx
lemma dark (A:Panel F){x:Points m} (hx:x∉conf m): A.off d x=0:= dif_neg hx
-- smooth property at this level only means continuous with any field at any fixed family. Avoid needing derivatives in interpolation: test profiles.Adapters later optional.
def clearP (A:Panel F): Prop:=∀d m n (v:Fin m→ E F d), ContinuousOn (fun t:Points m=> PayAll.taste (A.off d t) v n) (conf m)
def lives (A:Panel F)(d k:ℕ) : Bank F d:= fun _ s=> PositionX.Bare.spread (sameAxis F d) (fun v=> s.applyTo (fun t=> PayAll.taste (A.off d t) (sameAxis F d∘v) k ))
lemma newly (p:Test m)(v:Fin m→ E F d)(k:ℕ) (h:A.clearP) : A.lives d k m p v=p.applyTo (fun t=>Panel.off A d t k v):= by
    let U:= sameAxis F d; rw [lives, PositionX.Bare.spread_value ]; unfold Test.applyTo; have he (y:Points m): Panel.off A d y k v=∑ i:Fin m→ BasisIx G d,(∏ j,U.coord (i j) ( v j )) * PayAll.taste ( A.off d y ) ( U ∘ i ) k:= WorldJet.countr F U (Panel.off A d y k) v;
    simp_rw [ he, Finset.mul_sum,mul_left_comm (p _) ]; rw [ MeasureTheory.integral_finsetSum _ (fun i _=>?_ ) ]; simp_rw [ integral_const_mul ]; rfl; exact (p.smearing (K:=fun t=>PayAll.taste (A.off d t) (U∘_) k) ( h d m k (U ∘ i) )).const_mul _
@[ext] lemma ext {A B:Panel F} (h:∀d m (x:Polyp m),A.out d x=B.out d x): A=B:= by cases A; cases B; congr; funext d m x; exact h ..
lemma chain_real (hp:A.clearP)(hx:B.clearP)(h: A.lives = B.lives): A=B:= by
    apply ext; intro d m x; funext k; ext1 v; obtain hv: ∀ p:Test m,p.applyTo (fun t=> A.off d t k v)= p.applyTo (fun t=> B.off d t k v):= by intro p; rw [← newly A p v k hp, ← newly B p v k hx,h ];
    have he:= ( Test.unique_kernel ( hp d m k v ) ( hx d m k v ) ).1 hv; have ht : A.off d x k v=B.off d x k v:= he x.property; rwa [sees _ x.property,sees _ x.property ] at ht
-- recurrent scaling actions
variable {ξ:Strat F}
def flip (P:Panel F)(ξ:Strat F) : Panel F:= ⟨fun d {_} x=> heated (P.out d x) (ξ.wire d) ⟩
def join (P:Panel F) (v: Word ℝ): Panel F:= ⟨ fun d {_} x=> Jet.ren v (P.out d x) ⟩
def cZ (v:ℝ)(x: Points m): Points m:= Real.exp (-v) • x
def shiftP (v:ℝ)(x: Polyp m): Polyp m:= ⟨ cZ v x.1,(fun _ _ he=> ( x.property: Injective x.1.ofLp ) (smul_right_injective _ ((Real.exp_pos (-v)).ne') he )) ⟩
def slide (A:Panel F)(s:ℝ): Panel F:= ⟨ fun d _ x=>A.out d (shiftP s x) ⟩
lemma moved_t (s t:ℝ)(x:Polyp m): shiftP s (shiftP t x) = shiftP (s+t) x:= by ext1; change Real.exp _ • (Real.exp _ • x.val) = Real.exp _ • _; rw [ smul_smul, ← Real.exp_add ]; simp only [ neg_add ]
lemma slide_steps (s t:ℝ) : (A.slide s).slide t=A.slide (s+t):= ext fun _ _ x=> congr_arg _ (moved_t s t x)
lemma slide_t (s:ℝ): (slide A s).off d (x:Points m)=A.off d ( cZ s x.1 ):= by rw [ sees _ x.property, sees _ (show cZ s x.1 ∈ conf _ from (shiftP ..).property ) ]; rfl
lemma slide0 : A.slide 0=A:= by
    apply ext; intro d m x; change A.out d (shiftP 0 x)= A.out d x; apply congr_arg; ext1; simp [shiftP,cZ]
lemma flip_slide (s:ℝ): (A.slide s).flip T=(A.flip T).slide s:= rfl
lemma join_slide (s:ℝ): (A.slide s).join φ=(A.join φ).slide s:= rfl
lemma flip_mul (u v: Strat F): (A.flip u).flip v=A.flip (u*v):= ext fun d _ x=> PayAll.occupies ( A.out d x ) _ _
lemma leading : A.flip 1=A:= ext (fun d _ x=> by change heated ( A.out d x ) ( wire ( 1:Strat F ) d ) =_; rw [zeroed, town0] )
lemma join_flip (h: light φ) : (A.flip T).join φ=(A.join φ).flip ( T.resume φ ):= ext (fun d _ x=> PayAll.gathers ( A.out d x ) (T.wire d) _ h )
lemma join_step (v: Word ℝ)(h:light φ)(hx:light v) : (A.join φ).join v = A.join (ren v φ):= by
    apply ext; intro d m x; funext k; ext1 p; let X:=A.out d x; let f:= PayAll.value p ( F:=F ) (d:=d); change ( f ∘ ren v ( ren φ X ) ) k= ( f ∘ ren (ren v φ) X ) k; rw [ren_writes, ren_writes, ren_writes,Jet.asc ( V:=ℂ ) hx h ]; --
lemma join_id : A.join headway=A:= by
    apply ext; intro d m x; funext k; ext1 p; let f:=PayAll.value (F:=F) (d:=d) p; change (f∘ren headway ( A.out d x )) k=_; rw [ ren_writes, Jet.ren_head ( V:=ℂ ) ]; rfl
-- `PayAll.slit`. Expand both actions, commute limits etc.
private def assemble (f:PayAll.reprK F d m) : Court ( E F d ) m (PowerSeries ℂ):= (raiseW).compMultilinearMap (MultilinearMap.pi (R:=ℂ) f) -- name?
lemma repr_h (p: Fin m → E F d)(a:Word (Buffer F d)) (n:ℕ) : heated f a n p= ∑ i: Fin m→ BasisIx G d,∑ j∈Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff (R:=ℂ) j.1 ( WorldJet.rentF F a (ColorCode.sameAxis F d) i p ) * f j.2 ( ColorCode.sameAxis F d ∘ i ):= by
    let Q:=sameAxis F d; let L:= assemble f;
    have he(i:ℕ) (u): coeff (R:=ℂ) i ( L u )= f i u:= congr_fun (saving (fun i=> f i u)) i
    rw [ ← PayAll.slit f a L p (fun i=> MultilinearMap.ext fun u=>(he i u).symm), drag,_root_.sum_apply,map_sum ];-- lift notation.
    refine Finset.sum_congr rfl fun i hi=>?_ ; change coeff (R:=ℂ) n (_ * _)= _; rw [ coeff_mul ]; simp_rw [ he ]; -- may need annotate
lemma ren_blank (v:Word ℝ): ren v (0:PayAll.reprK F d m)=0:= by funext j; unfold ren Jet.order; simp
lemma hum_zero (a:Word (Buffer F d)) : heated (0:PayAll.reprK F d m) a=0:= by funext k; ext1 p; rw [repr_h]; simp
lemma tape (p: Points m): (A.flip T).off d p=heated (A.off d p) (T.wire d):= by unfold off; split; rfl; rw [hum_zero ]
lemma tale (p: Points m): (A.join φ).off d p= ren φ (A.off d p):= by unfold off; split; rfl; rw [ren_blank ]
lemma night (h:A.clearP) : (A.flip T).clearP:= by
   intro d m n v; unfold taste; simp_rw [ tape, repr_h ]; refine continuousOn_finsetSum _ (fun i _=> continuousOn_finsetSum _ (fun j _=> ?_)); exact continuousOn_const.mul ( h d m j.2 (sameAxis F d ∘ i) ) -- name
lemma bright (h:A.clearP): (A.join φ).clearP:= by
   intro d m n v; simp_rw [ tale, show ∀ f:PayAll.reprK F d m, PayAll.taste (ren φ f) v n= _ from fun f=>congr_fun (PayAll.value_ren f φ v) n ]; unfold ren Jet.order; refine continuousOn_const.smul ( continuousOn_finsetSum _ (fun j _=>?_)); exact continuousOn_const.smul (continuousOn_const.smul ( h _ _ _ _ ))
lemma skim (h:A.clearP)(v:ℝ): (A.slide v).clearP:= by
   intro d m n p
   refine ContinuousOn.congr ( (h d m n p).comp (f:=cZ v) (g:=(fun x=> PayAll.taste (A.off d x) p n)) ?_ ?_ ) ?_; -- no FieldPorches remove
   · exact Continuous.continuousOn (show Continuous (cZ (m:=m) v) from continuous_const.smul (f:=fun _:Points m=>Real.exp (-v)) (g:=(id:Points m→_)) continuous_id)
   · exact fun _ hx=> (shiftP v ⟨_,hx⟩ ).property
   intro x hx; exact congr_arg (fun t=> PayAll.taste t p n) (slide_t A (x:=⟨x,hx⟩) v)
lemma turn_book (h:A.clearP): (A.flip T).lives d=predMarket (T.wire d) (A.lives d):= by
   funext k m p; ext1 v; rw [ newly _ p v k ( night A T h ), show predMarket _ _ k _ _ _=heated ( PayAll.ploy p ∘ A.lives d ) (T.wire d) k v from DFunLike.congr_fun (Eq.symm (PayAll.myTip _ (T.wire d) k p (A.lives d) rfl)) v ]; let S(i:Fin m→BasisIx G d):= WorldJet.rentF F (T.wire d) (sameAxis F d) i v;
   simp_rw [ tape,repr_h ]; have he (i:Fin m→ BasisIx G d ) (w:ℕ): ( ( PayAll.ploy p ∘ A.lives d ) w ) ( sameAxis F d ∘ i )= p.applyTo (fun t=>A.off d t w (sameAxis F d ∘ i)):= newly A p _ w h; simp_rw [he,Test.applyTo, Finset.mul_sum, mul_left_comm (p _) (coeff (R:=ℂ) _ _), ← integral_const_mul ];
   rw [MeasureTheory.integral_finsetSum _ (fun i _=>?_ ) ]; -- maybe expensive.
   · exact Finset.sum_congr rfl fun i _=> MeasureTheory.integral_finsetSum _ (fun j _=> ( p.smearing ( h _ _ j.2 ( sameAxis F d ∘ i ) ) ).const_mul _)
   exact integrable_finsetSum _ (fun j _=> ( p.smearing (h _ _ j.2 ( sameAxis F d ∘ i ) ) ).const_mul _ ) -- implicit T
lemma total_book (h:A.clearP): (A.join φ).lives d=Jet.ren φ ( A.lives d ):= by
   funext k m p; ext1 v; let Q:=lookie F ⟨ m,v,p ⟩ ( d:=d ); change _=(Q ∘ Jet.ren φ ( A.lives d )) k;
   rw [ newly _ p v k ( bright A φ h ),ren_writes ]; let t(n:ℕ)(x:Points m):= PayAll.taste ( A.off d x ) v n; let u:= Q ∘ A.lives d; have hx(n): u n=p.applyTo ( t n ):= newly A p v n h;
   let K(j: OrderedFinpartition k):ℝ:= (∏ l, ( ( ( j.partSize l).factorial : ℕ ):ℝ) * φ (j.partSize l) ) * ( (j.length.factorial:ℕ):ℝ ); let J(n:ℕ):=(n.factorial:ℝ)⁻¹;
   have hr(w:Word ℂ): Jet.ren φ w k= J k • (∑ j:OrderedFinpartition k,K j • w j.length):= by unfold J K; simp_rw [mul_smul]; rfl;
   change p.applyTo (fun t=> PayAll.taste ((A.join φ).off d t) v k)=ren φ u k;
   simp_rw [tale,show ∀ f:PayAll.reprK F d m, PayAll.taste (ren φ f) v k= _ from fun f=>congr_fun (PayAll.value_ren f φ v) k,hr, hx,Test.applyTo ]; simp_rw [Complex.real_smul, mul_left_comm (p _), Finset.mul_sum, mul_left_comm (p _) ( K _ :ℂ) ]; rw [MeasureTheory.integral_finsetSum ]; simp_rw [integral_const_mul ]; rfl; exact fun b _=> (( p.smearing ( h _ _ b.length v ) ).const_mul _).const_mul _
end Panel
end YM.FVA2
