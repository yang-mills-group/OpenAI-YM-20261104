import YM.OPE.Measuring.Wedge

/-! Finite tree coordinate chart using literal parent-ratio variables. No
lower bounds on a declared edge size. Narrow-topped trees studied for the
regular-germ estimate contain only unary or empty forks (finite depth). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Tree
open Nesting Nesting.Tree Filter Set Function
open scoped Topology ContDiff

def Narrow (t:Tree) : Prop := match t with
 | bud=> True
 | .fork n f=> n≤ 1∧ ∀i:Fin n,Narrow (f i)

variable {n:ℕ}{f:Fin n→Tree}{t:Tree}
lemma under_narrow (ht:Narrow (.fork n f))(i:Fin n): Narrow (f i):=ht.2 i
lemma branch_sub (ht:Narrow (.fork n f)):Subsingleton (Fin n):=⟨fun a b=>Fin.ext (by have ha:=a.isLt; have hb:=b.isLt; have h:=ht.1; omega)⟩
lemma leaf_sub (ht:Narrow t):Subsingleton t.Leaf:=by
    induction t with
    | bud=>exact Subsingleton.intro (fun (a b:Unit)=>Subsingleton.elim a b)
    | fork n f ih=> constructor; intro a b; rcases a with ⟨i,a⟩; rcases b with ⟨j,b⟩
                    obtain rfl : i = (j:Fin n) :=(branch_sub ht).allEq _ _
                    congr 1; exact (ih _ (ht.2 _)).allEq _ _

def sizes : (t:Tree)→ℝ→(t.Inner→ℝ)→ t.Inner→ℝ
 | bud,_p,_r,x=> nomatch x
 | fork n _f,p,r,.inl _=> p*r (.inl ())
 | fork n f,p,r,.inr ⟨i,v⟩=>sizes (f i) (p*r (.inl ())) (childAge i r) v

def model : (t:Tree)→ℝ→(t.Inner→ℝ)→ t.Plot→t.Plot
 | bud,p,_,z,x=>p • z x
 | fork n f,p,_r,z,.inl _=>p • z (.inl ())
 | fork n f,p,r,z,.inr ⟨i,x⟩=>p • z (.inl ())+model (f i) (p*r (.inl ())) (childAge i r) (childPlace i z) x

lemma sizes_good {p:ℝ}{r:t.Inner→ℝ}(hp:0<p)(he:∀ v,r v∈Ioc (0:ℝ) 1): Tapered t p 1 (sizes t p r):=by
     induction t generalizing p with
     | bud=>exact True.intro
     | fork n f ih=> exact ⟨mul_pos hp (he _).1, ((mul_le_mul_of_nonneg_left (he _).2 hp.le).trans_eq (mul_one _)), fun i=>(by exact Eq.mpr (by rw [mul_one]; rfl) (show Tapered (f i) (p*r (.inl ())) 1 (sizes (f i) _ (childAge i r)) from ih i (mul_pos hp (he _).1) (fun v=>he (Sum.inr ⟨i,v⟩))))⟩
lemma sizes_ratios {p:ℝ}{u:t.Inner→ℝ}(hp:p≠0)(he:∀i:t.Inner,u i≠0):t.ratios p (sizes t p u)=u:=by
     induction t generalizing p with
     | bud=>exact funext (fun i=> nomatch i)
     | fork n f ih=> funext i; rcases i with a|⟨j,i⟩
                     · cases a; change p*u _ / p=_; field_simp
                     exact congr_fun (ih j (u:=childAge j u) (mul_ne_zero hp (he _)) (fun i=>he (Sum.inr ⟨j,i⟩))) i

lemma recover_sizes {p:ℝ}{u:t.Inner→ℝ}(hp:0<p)(hu:∀i,0<u i):sizes t p (t.ratios p u)=u:=by
     induction t generalizing p with
     | bud=>exact funext (fun i=> nomatch i)
     | fork n f ih=>funext i; have he:p*(u (.inl ())/p) = u (Sum.inl ()) := mul_div_cancel₀ _ hp.ne'
                    rcases i with ⟨⟩ | ⟨j,v⟩; exact he; change sizes (f j) (p*(u (Sum.inl ())/p)) _ v=_; rw [he]; exact congr_fun (ih j (p:=u (.inl ())) (hu _) (fun i=>hu (Sum.inr ⟨j,i⟩))) v
lemma tempered {p:ℝ}{u:t.Inner→ℝ}(hp:Tapered t p 1 u)(h:0 < p)(i:t.Inner): t.ratios p u i∈Ioc (0:ℝ) 1:=by
     induction t generalizing p with
     | bud=> cases i
     | fork n f ih=> rcases i with ⟨⟩|⟨j,v⟩; exact ⟨div_pos (hp.positive _) h, (div_le_one h).mpr hp.2.1⟩; exact ih j (p:=u (.inl ())) (by convert hp.2.2 j using 1; exact (mul_one _).symm) (hp.positive _) v

lemma anchor_model {p:ℝ}{r:t.Inner→ℝ}(z:t.Plot):anchor (model t p r z)=p• anchor z:=by cases t <;> rfl

variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
lemma model_smooth (t:Tree){p:V→ℝ}{r:V→t.Inner→ℝ}{z:V→t.Plot} (hp:ContDiff ℝ ∞ p)(hr:∀j:t.Inner,ContDiff ℝ ∞ (fun v=>r v j))(hz:∀x:t.Positions,ContDiff ℝ ∞ (fun v=>z v x)):ContDiff ℝ ∞ (fun v=>model t (p v) (r v) (z v)):=by
     induction t generalizing p with
     | bud=>exact contDiff_pi.mpr (fun (u:Unit)=>hp.smul (hz u))
     | fork n f ih=> refine contDiff_pi.mpr ?_; rintro (j|⟨i,x⟩)
                     · cases j; exact hp.smul (hz (.inl ()))
                     exact (hp.smul (hz (.inl ()))).add ((contDiff_pi.mp (ih i (hp.mul (hr (.inl ()))) (fun x=>hr (.inr ⟨i,x⟩)) (fun x=>hz (.inr ⟨i,x⟩)))) x)


def inverse : (t:Tree) → ℝ → (t.Inner→ℝ) → t.Plot → E4→t.Plot
 | bud,p,_a,z,o,j=>p⁻¹ • (z j-o)
 | fork _ _,p,_a,z,o,.inl u => p⁻¹ • (z (Sum.inl u)-o)
 | fork _ f,p,a,z,o,.inr ⟨j,v⟩ => inverse (f j) (a (Sum.inl ())) (childAge j a) (childPlace j z) (anchor z) v

lemma centered (t:Tree){p:ℝ}{a:t.Inner→ℝ} (z:t.Plot) (u:E4) (hp:p≠0)(ha:∀j,a j≠0): model t p (t.ratios p a) (inverse t p a z u) = fun v=> z v-u :=by
    induction t generalizing p u with
    | bud=> funext v; rw [model,inverse,smul_inv_smul₀ hp]
    | fork n f ih=> funext v; rcases v with ⟨⟩|⟨i,v⟩
                    · rw [model,inverse,smul_inv_smul₀ hp]
                    rw [model,inverse,smul_inv_smul₀ hp,show p*(fork n f).ratios p a (.inl ())=a (Sum.inl ()) by rw [ratios, mul_div_cancel₀ _ hp]]
                    change _ + model (f i) _ ((f i).ratios _ (childAge i a)) (inverse (f i) _ _ _ _) v=_; rw [ih i _ _ (ha _) (fun j=>ha _)]; unfold anchor childPlace topSeat; exact sub_add_sub_cancel' (z (Sum.inl ())) u (z (Sum.inr ⟨i,v⟩)) 
lemma fit {p M η:ℝ}{a:t.Inner→ℝ}{z:t.Plot}{u:E4}(hp:0<p)(ha:Tapered t p 1 a)(hm:Immediate M η t a z)(hz:‖anchor z-u‖ ≤ M*p) (v:t.Positions):‖inverse t p a z u v‖ ≤ max M 1 := by
    induction t generalizing p u with
    | bud=> change Unit at v; cases v; change ‖p⁻¹•(anchor z-u)‖ ≤ max M 1
            rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le]; exact ((mul_le_mul_of_nonneg_left hz (inv_pos.mpr hp).le).trans_eq (by field_simp)).trans (le_max_left ..)
    | fork n f ih=> rcases v with ⟨⟩|⟨i,v⟩
                    · change ‖p⁻¹•(anchor z-u)‖ ≤ max M 1; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le]; exact ((mul_le_mul_of_nonneg_left hz (inv_pos.mpr hp).le).trans_eq (by field_simp)).trans (le_max_left ..)
                    exact ih i (ha.positive _) ((mul_one _).trans (Eq.refl (a (Sum.inl ()))) ▸ ha.2.2 i) (hm.2.2 i) (hm.1 i) _

lemma on_model (t:Nesting.Tree) {p M η:ℝ}{r:t.Inner→ℝ}(z:t.Plot)(ht:Narrow t)(hr:∀v,r v∈Ioc (0:ℝ) 1)(hp:0<p)(hM:0 ≤ M)(hb:∀q,‖z q‖ ≤ M):Tree.Immediate M η t (sizes t p r) (model t p r z) := by
    induction t generalizing p with
    | bud=>exact True.intro
    | fork n f ih=>
       let s:=p*r (Sum.inl ()); have hs:0<s:=mul_pos hp (hr _).1
       refine ⟨fun j=>?_,fun i j hij=> (hij ((branch_sub ht).allEq ..)).elim,fun j=> ?_⟩
       · change ‖(p•z (.inl ()) + model (f j) s _ _ _)-p•z (.inl ())‖ ≤ M*s; rw [add_sub_cancel_left]; change ‖anchor (model (f j) s (childAge j r) (childPlace j z))‖ ≤ _; rw [anchor_model (p:=s) (r:=childAge j r) (childPlace j z),norm_smul,Real.norm_of_nonneg hs.le,mul_comm]; exact mul_le_mul_of_nonneg_right (hb _) hs.le
       have hh:= ih j (z:=childPlace j z) (ht.2 j) (fun i=>hr (Sum.inr ⟨j,i⟩)) hs (fun i=>(hb (Sum.inr ⟨j,i⟩))) -- implicit hM
       change Immediate M η (f j) _ (fun i => p • z (.inl ()) + model (f j) s (childAge j r) (childPlace j z) i)
       exact immediate_shift _ _ (p • z (.inl ())) hh
where immediate_shift (t:Nesting.Tree)(z:t.Plot)(x:E4){a:t.Inner→ℝ} (h:Immediate M η t a z) : Immediate M η t a (fun i=>x+z i) :=by
       induction t generalizing x with
       | bud=>exact True.intro
       | fork _ f ih=>refine ⟨fun i=> ?_,fun i j hj=>?_,fun i=>ih i _ _ (h.2.2 i)⟩
                      · calc _ = ‖z (.inr ⟨i,(f i).topSeat⟩)-z (.inl ())‖:=congr_arg norm (show x+z _-(x+z _)=_ from by abel)
                             _ ≤ _ := h.1 i
                      exact (h.2.1 i j hj).trans_eq (congr_arg norm (show z _ - z _=(x+z _)-(x+z _) by abel))
end YM.OPE.Measuring.Tree
