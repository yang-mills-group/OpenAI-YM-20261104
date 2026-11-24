import YM.RegulatorIR.Binding.Zero

/-! Rotation-linear data for top Hessian and for bonds. Anchor claims concern
only energy/gauge orbits on the inversion *regulator* and not anomalous
cancellations in any physical expansion. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision Work
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {f c: Side} {G:Gauge}

lemma fire_closed {u:Horizon G f} (hf: Even f.val) (h:Orb.Closed (fire u)): GradientSite u:=by
 have he: Orb.InvLink (fire u):= by rintro ⟨x,i⟩; change -(fire u (reflect (x,i)))=_; rw [fire_swaps u hf,neg_neg]
 obtain ⟨k,hk,hd⟩:= Orb.exact_curl (A:=fire u) he h
 have Hk : EvenSite k:=by
   have hp (w x):cash (fire u) w x = k (x+Lattice.Step.vec w)-k x:= by
      cases w with | mk i b=>cases b <;> simp [cash,Lattice.Step.used,hd,Lattice.Step.vec,sub_eq_add_neg,add_comm]
   have hy (w: Walk) x : line (fire u) x w=k (stop x w)-k x:=by
      induction w generalizing x with
      | nil=> simp [Orb.line,Lattice.stop]
      | cons i v ih=>rw [Orb.line,hp i,ih,stop]; abel
   intro i; let W:=arrival i
   have hz:= Orb.inv_line he W 0; simp_rw [hy,hk] at hz;rw [Orb.stop_flip,arrival_end] at hz; simpa [hk] using hz
 refine ⟨-k, (fun i=> by simp only [Pi.neg_apply,Hk i]),?_⟩; ext1 i
 rw [← fire_at u i]; unfold gradie; rw [hd]; simp; abel
lemma grad_closed {u:Horizon G f}(hf: Even f.val)(h:GradientSite u): Orb.Closed (fire u):=by
 obtain ⟨k,hk,rfl⟩:=h; intro i x y; unfold Orb.Curl; simp_rw [gradie_uses k hk hf]; rw [add_right_comm i]; abel

-- Pay pre-orbit Wilson energy without exponential

def valueO (U:Shape G f):ℝ:=energy (orbLift U)/2
def plume (x:Horizon G f)(p: Face (Per f)) : G.Color:= Orb.Curl (fire x) p.1 p.2.val.1 p.2.val.2
-- quadratic homogeneous

def costO (x:Horizon G f) : ℝ:= (∑ v, ‖plume x v‖^2/2)/2
lemma costO_pos (x:Horizon G f):0≤costO x:=by unfold costO; positivity
lemma costO_null (x:Horizon G f)(hf:Even f.val)(h:costO x=0): GradientSite x:=by
 have H p : plume x p=0:=by
   have hv:= (Finset.sum_eq_zero_iff_of_nonneg (fun (y : Face (Per f)) _=>show 0≤‖plume x y‖^2/2 by positivity)).mp ((div_eq_zero_iff.mp h).resolve_right (by norm_num)) p (Finset.mem_univ _); exact norm_eq_zero.mp (by nlinarith)
 apply fire_closed hf; intro i j k
 rcases lt_trichotomy j k with ht|ht|ht
 · exact H (i,⟨(j,k),ht⟩)
 · subst k; unfold Orb.Curl;abel
 have he: Orb.Curl (fire x) i k j = 0:= H (i,⟨(k,j),ht⟩); rw [show Orb.Curl _ i j k= -Orb.Curl (fire x) i k j by unfold Orb.Curl;abel]; rw [he,neg_zero]
lemma CostP (x:Horizon G f)(p:Face (Per f)): plume x p= F03.faceCurl p (canvas x):=by
 unfold F03.faceCurl
 rw [← fundamental];
 change Orb.Curl _ p.1 _ _= linkSum _ _ _; rw [← Orb.face_line];
 have hv e : collect G (canvas x) e=fire x e:=by rcases e with ⟨i,j⟩; change fire _ (i,axisEquiv.symm (axisEquiv j))=_; rw [show axisEquiv.symm _ = j from axisEquiv.symm_apply_apply j]
 have hh (w i): line (fire x) i w=linkSum (collect G (canvas x)) i w:=by
    induction w generalizing i with
    | nil=> rfl
    | cons d w ih=> rw [Orb.line,ih,cash,linkSum]; split <;> rw [hv]
 exact hh ..
lemma CostC (x:Horizon G f):Tendsto (fun t:ℝ=> valueO (climb (t • x))/t^2) (𝓝[≠] 0) (𝓝 (costO x)) := by
 unfold valueO; simp_rw [mat_expanded,canvas_rate,energy]
 let A(t:ℝ):= represent (t • canvas x)
 have he(t:ℝ): (∑ b:Face (Per f),G.price (faceValue (A t) b))/2/t^2=(∑ b:Face (Per f),G.price (faceValue (A t) b)/t^2)/2:=by rw [← Finset.sum_div, div_right_comm]
 change Tendsto (fun t:ℝ=>(∑ b:Face (Per f), G.price (faceValue (A t) b))/2/t^2) _ _; simp_rw [he]; unfold costO
 apply Tendsto.div_const
 refine tendsto_finsetSum _ fun i _=>?_
 rw [CostP];apply F03.price_limit _ (F03.face_deriv i (canvas x))
 rw [zero_smul,Precision.link_one,faceValue];exact anyWalk ..
lemma valueZero : valueO (1:Shape G f)=0:=by
 unfold valueO; rw [Geometry.lift_one]; unfold energy;simp_rw [faceValue, anyWalk]; simp
lemma valueSmooth : ContDiffAt ℝ ω (fun x:Horizon G f=>valueO (climb x)) 0:=by
 unfold valueO energy; apply ContDiffAt.div_const; apply ContDiffAt.sum;intro i _;simp_rw [mat_expanded]; apply Work.F03.price_smooth; unfold faceValue
 refine (show ContDiffAt ℝ ω (fun a=>G.mat (travel (represent a) i.1 _)) (canvas (0:Horizon G f)) from ?_).comp _ canvased
 rw [canvas_origin]; exact Push.writes ..
end YM.RegulatorIR.Binding
