import YM.Contacts.Barrage.Trophy
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Wire
abbrev wire (v:E)(f:E→ℝ) := fun x => fderiv ℝ f x v
def tack (v:E)(f:E→ℝ) (n:ℕ):= (wire v)^[n] f
lemma tack_now (v:E)(f:E→ℝ)(n:ℕ):tack v f (n+1)=wire v (tack v f n) := by unfold tack; rw [Function.iterate_succ_apply']
lemma tack_wire (v:E)(f:E→ℝ)(n:ℕ): tack v (wire v f) n=tack v f (n+1):= rfl -- ?
lemma wire_fiber (v:E)(h:AnalyticAt ℝ a t): AnalyticAt ℝ (wire v a) t := ContDiffAt.analyticAt ((h.contDiffAt.fderiv_right (m:=ω) le_top).clm_apply contDiffAt_const)
lemma tack_fiber (v:E)(h:AnalyticAt ℝ a t)(n:ℕ): AnalyticAt ℝ (tack v a n) t:= by induction n with|zero=>exact h|succ n ih=>rw [tack_now];apply wire_fiber _ ih
lemma wire_symmetric {t:E}(h:AnalyticAt ℝ a t)(v w:E): wire v (wire w a) t= wire w (wire v a) t:= by
   have he := h.contDiffAt.isSymmSndFDerivAt_of_omega v w; unfold wire; let K(x:E):=fderiv ℝ a x; have hh (v w:E): fderiv ℝ (fun x=> K x v) t w=(fderiv ℝ K t w) v:= by
     let L:=ContinuousLinearMap.apply ℝ ℝ v; change fderiv ℝ (L ∘ K) t w=_; rw [(L.hasFDerivAt.comp t ((show DifferentiableAt ℝ K t from (h.contDiffAt.fderiv_right (m:=ω) le_top).differentiableAt (by simp)).hasFDerivAt)).fderiv]; rfl
   exact (hh w v|>.trans he).trans (hh v w).symm
lemma tack_cong {t:E} (h: a=ᶠ[𝓝 t] b)(v:E)(n:ℕ): tack v a n=ᶠ[𝓝 t] tack v b n:= by induction n with|zero=>exact h|succ n ih=>rw [tack_now,tack_now];exact (ih.fderiv (𝕜:=ℝ)).mono fun _ hx=> congr_arg (fun p:_→L[ℝ] ℝ=>p v) hx
lemma tack_value (v:E)(h:AnalyticAt ℝ a t)(n:ℕ): tack v a n t=iteratedFDeriv ℝ n a t (fun _=>v):= by
   induction n generalizing t with
   | zero => exact (iteratedFDeriv_zero_apply ..).symm
   | succ n ih=>
       have ht : AnalyticAt ℝ (iteratedFDeriv ℝ n a) t:= (h.contDiffAt.iteratedFDeriv_right (m:=ω) le_top).analyticAt
       rw [tack_now, ht.differentiableAt.iteratedFDeriv_succ_apply_left']; exact congr_arg (fun p:_→L[ℝ] ℝ=> p v) ((show tack v a n=ᶠ[𝓝 t] (fun x=>iteratedFDeriv ℝ n a x (fun _=>v)) from h.eventually_analyticAt.mono fun _ h=>ih h).fderiv_eq)
lemma tack_add {t:E}(v:E)(h:AnalyticAt ℝ a t)(he:AnalyticAt ℝ b t)(n:ℕ) : tack v (a+b) n t=tack v a n t+tack v b n t:= by rw [tack_value _ (h.add he),tack_value _ h,tack_value _ he,iteratedFDeriv_add_apply h.contDiffAt he.contDiffAt]; rfl
lemma commute {t:E}(h: AnalyticAt ℝ a t)(v w:E)(n:ℕ): tack w (wire v a) n t=wire v (tack w a n) t:= by
   induction n generalizing t with
   | zero =>rfl
   | succ n ih=> rw [tack_now,tack_now]; rw [show wire w _ t=_ from (show _=wire w (wire v (tack w a n)) t from congr_arg (fun p:_→L[ℝ] ℝ=>p w) ((show tack w (wire v a) n=ᶠ[𝓝 t] wire v (tack w a n) from h.eventually_analyticAt.mono fun _ h=> ih h).fderiv_eq))]; exact wire_symmetric (tack_fiber w h _) w v
section shuffle
variable {v:V}{u:E×V→ℝ}
local notation "Α" => (E×V)
abbrev cat (y:V):Α→Α:=fun i=>(i.1,y)
abbrev vx (y:V):Α:= (0,y)
abbrev hy (x:E):Α:= (x,0)
def avoid (F: Α→ℝ)(y:V)(s:ℕ):Prop:= ∀ i:ℕ,i<s→∀ᶠ x:E in 𝓝 0, tack (vx y) F i (x,0)=0
lemma clear_vert (F: Α→ℝ){a:Α}(he: AnalyticAt ℝ F a)(w:V): wire (vx (E:=E) w) F a= wire w (fun y=> F (a.1,y)) a.2:= by
   let L:= ContinuousLinearMap.inr ℝ E V; have ht: HasFDerivAt (fun y=> (a.1,y)) L a.2:= (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _); unfold wire; rw [(show HasFDerivAt (fun y=>F (a.1,y)) ((fderiv ℝ F a).comp L) a.2 from he.differentiableAt.hasFDerivAt.comp _ ht).fderiv]; rfl
lemma clear_horizon (F: Α→ℝ){a:Α}(he:AnalyticAt ℝ F a)(w:E): wire (hy (V:=V) w) F a= wire w (fun x=> F (x,a.2)) a.1:= by
   let L:= ContinuousLinearMap.inl ℝ E V; have ht: HasFDerivAt (fun y=> (y,a.2)) L a.1:= (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _); unfold wire; rw [(show HasFDerivAt (fun y=>F (y,a.2)) ((fderiv ℝ F a).comp L) a.1 from he.differentiableAt.hasFDerivAt.comp _ ht).fderiv]; rfl
lemma tack_vert (F:Α→ℝ){a:Α}(he:AnalyticAt ℝ F a)(v:V)(n:ℕ): tack (vx v) F n a= tack v (fun y=> F (a.1,y)) n a.2:= by
   induction n generalizing a with|zero=>rfl|succ n ih=>
   rw [tack_now,tack_now,clear_vert _ (tack_fiber (vx v) he _)]; have hh:= ((show Tendsto (fun y:V=>(a.1,y)) (𝓝 a.2) (𝓝 a) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually he.eventually_analyticAt); exact congr_arg (fun p:_ →L[ℝ] ℝ=> p v) ((show (fun y=> tack (vx v) F n (a.1,y))=ᶠ[𝓝 a.2] tack v (fun y=>F (a.1,y)) n from hh.mono fun y hy=> ih (a:=(a.1,y)) hy).fderiv_eq)
lemma avoid_front (h: avoid u v k)(i:ℕ)(he:i≤k): avoid u v i:= fun j hh=> h j (hh.trans_le he)
lemma evade_h (h:avoid u v k)(he:AnalyticAt ℝ u 0)(x:E): avoid (wire (hy x) u) v k:= by
   intro i hi; let f:=tack (vx v) u i; let K (x:E):=(x,(0:V)); have hx:(fun x=> f (K x))=ᶠ[𝓝 0] 0:= h i hi
   have ht: Tendsto K (𝓝 0) (𝓝 0):= tendsto_id.prodMk_nhds tendsto_const_nhds
   filter_upwards [hx.fderiv (𝕜:=ℝ), ht.eventually he.eventually_analyticAt] with z hz he; change tack _ _ _ (K z)=_; rw [commute he (hy x) (vx v) i, clear_horizon _ (tack_fiber _ he _)]; rw [show fderiv ℝ (0:E→ℝ)=0 from funext fun i=> fderiv_const_apply ..] at hz; unfold wire; erw [hz]; rfl
lemma evade_v (h:avoid u v (k+1)): avoid (wire (vx v) u) v k:= fun i hi=> h (i+1) (Nat.succ_lt_succ hi)
-- Leading polynomial in pure v
lemma evades (k:ℕ)(h:avoid u v k)(he:AnalyticAt ℝ u 0)(x:E): tack (x,v) u k 0=tack (vx v) u k 0:= by
    induction k generalizing u with
    | zero=>rfl
    | succ k ih=>
       rw [← tack_wire (x,v), ← tack_wire (vx v)]; let a:=wire (hy x) u; let b:=wire (vx v) u; have ht:= evade_h h he x; have hy: AnalyticAt ℝ a 0:= wire_fiber _ he; rw [show wire (x,v) u=a+b from funext fun z=> by rw [wire, show (x,v)=Wire.hy x + vx v from Prod.ext (add_zero _).symm (zero_add _).symm,map_add]; rfl, tack_add (x,v) hy (wire_fiber _ he)]
       have hv:tack (vx v) a k 0=0:= ((show (fun x:E=>tack (vx v) a k (x,0))=ᶠ[𝓝 0] 0 from ht k k.lt_succ_self).eq_of_nhds); rw [ih (avoid_front ht k k.le_succ) hy,ih (evade_v h) (wire_fiber _ he),hv,zero_add] -- swap threat
lemma jet_tack (F:E→ℝ)(h:AnalyticAt ℝ F 0) (i:ℕ)(x:E): jet F i x=(i.factorial:ℝ)⁻¹*tack x F i 0:= by rw [tack_value x h]; rfl
lemma seed (he:AnalyticAt ℝ u 0)(h:avoid u v k)(x:E): jet u k (x,v) = jet u k (0,v):= by rw [jet_tack _ he,evades k h he x, jet_tack _ he] 
lemma evade_jet (he:AnalyticAt ℝ u 0)(h:avoid u v k)(x:E)(i:ℕ)(hi:i<k): jet u i (x,v)=0 := by rw [seed he (avoid_front h i hi.le) x,jet_tack _ he]; erw [show _ = (0:ℝ) from ((show (fun x:E=> tack (vx v) u i (x,0))=ᶠ[𝓝 0] 0 from h i hi).eq_of_nhds),mul_zero] -- placeholder
def spiral (F:Α→ℝ):Α→ℝ:=fun x=> F (x.1,- x.2)
private def SW : Α →L[ℝ] Α:= (ContinuousLinearMap.fst ℝ E V).prod (-(ContinuousLinearMap.snd ℝ E V))
lemma lat (F:Α→ℝ)(h:AnalyticAt ℝ F 0): AnalyticAt ℝ (spiral F) 0 := Forge.starts _ h SW -- ambiguity
lemma lat_jet (F:Α→ℝ)(h:AnalyticAt ℝ F 0)(x:Α): jet (spiral F) n x= jet F n (x.1,-x.2):= woven h SW x n
private lemma scaled (x:V)(h:AnalyticAt ℝ u y)(n:ℕ)(c:ℝ): tack (vx (c • x)) u n y=c^n*tack (vx x) u n y:= by
   simp only [tack_value _ h]; rw [show vx (E:=E) (c • x) = c • vx x from Prod.ext (by change (0:E)=c • 0; simp) rfl]; erw [ContinuousMultilinearMap.map_smul_univ]; simp -- need function notation
lemma floor (he:AnalyticAt ℝ u 0)(v:V)(hp:Odd k)(hu:avoid u v k): avoid (u+spiral u) v (k+1):= by
   let s: E→Α:=hy; have hb:Tendsto s (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds; intro i hi;
   have hl (y:E) (g:AnalyticAt ℝ u (hy y)): AnalyticAt ℝ (spiral u) (hy y):= AnalyticAt.comp (f:=⇑(SW (E:=E) (V:=V))) (x:=hy y) (g:=u) (by simp only [show SW (hy y)=hy y from Prod.ext rfl (neg_zero : -(0:V)=0)]; exact g) ((SW (E:=E) (V:=V)).analyticAt _)
   have hh (y:E) (g:AnalyticAt ℝ u (hy y)): tack (vx v) (u+spiral u) i (hy y)=(1+(-1:ℝ)^i)*tack (vx v) u i (hy y):= by
      rw [tack_add _ g (hl y g)]; have he:tack (vx v) (spiral u) i (hy y)=tack (vx ((-1:ℝ) • v)) u i (hy y):= by
         rw [show (-1:ℝ) • v= -v from neg_one_smul ℝ v,tack_value _ g,tack_value _ (hl y g)]; unfold spiral; erw [show (fun x:Α=>u (x.1,-x.2))= u ∘ SW from rfl, wired (f:=u) (SW (E:=E) (V:=V)) (by simp [SW,hy,vx]; exact g)]; simp [SW,hy,vx]; rfl
      rw [he,scaled v g]; ring
   by_cases hv:i=k; swap; · filter_upwards [hu i (by omega),hb.eventually he.eventually_analyticAt] with y ht hg; rw [hh y hg,ht,mul_zero] -- under defeq hy?
   subst i; filter_upwards [hb.eventually he.eventually_analyticAt] with y ht; rw [hh y ht, hp.neg_one_pow]; ring
lemma spare (h:AnalyticAt ℝ u 0)(v:V)(hk:Odd k)(hp:avoid u v k)(x:E): jet u (k+1) (x,v)+jet u (k+1) (x,-v)= 2*jet u (k+1) (0,v):= by
   have he:= seed (h.add (lat _ h)) (floor h v hk hp) x; rw [serif h _ (lat _ h), serif h _ (lat _ h),lat_jet _ h,lat_jet _ h] at he; change _+jet _ _ (x,-v)= _+jet _ _ (0,-v) at he; refine he.trans ?_; rw [show (0,-v)= (-1:ℝ) • ((0:E),v) from by simp, jet_smul,pow_succ,hk.neg_one_pow]; ring -- find
end shuffle
end Wire
end
end YM.Contacts.Lintel
