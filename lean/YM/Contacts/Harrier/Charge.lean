import YM.Contacts.Harrier.Raft
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
-- repeatable size/sliding-step accounting. S side fixed while proving it. single stamp data common to both requests
open Mileage
variable {p q u:Word}{x:Dye G}{l': Pulse.Range (Node (Dye G))}
variable {H H': Sketch G→ℝ→Prop}
def Spent (D:ℕ)(x:Dye G)(ζ:ℝ≥0)(M:ℕ)(l : Pulse.Range (Node (Dye G)))(S:Boom)(H:Sketch G→ℝ→Prop)(F:Word→ Sketch G→Ribbon (Dye G) k) :Prop:=
   ∃ a≥(0:ℝ),∀ V:Sketch G, Living x M D V ζ → ∀ b≥(0:ℝ), H V b → (∀ i,OK S i→ Weight (F i V) D l x (a*b))∧∀ p q u, OK S p→OK S q→OK S u→ Weight (F (u++p) V-F (u++q) V) D l x (a*b*mileage u)
namespace Spent
variable {R W: Word→Sketch G→Ribbon (Dye G) k} {P:Sketch G}
lemma cast (h:Spent D x ζ M l' S H R)(he:∀ i K,Living x M D K ζ→ OK S i→W i K=R i K): Spent D x ζ M l' S H W:= by
   obtain ⟨a,ha,h⟩:=h; refine ⟨a,ha,fun V g b hb H=>⟨fun i hi=>?_,fun i j u hi hj hu=>?_⟩⟩; · rw [he _ _ g hi]; exact (h V g b hb H).1 _ hi
   rw [he _ _ g (hu.append hi),he _ _ g (hu.append hj)]; exact (h V g b hb H).2 i j u hi hj hu
lemma zero : Spent (k:=k) D x ζ M l' S H (fun _ _=>0):= by refine ⟨0,le_rfl,fun _ _ b _ _=>⟨fun i _=>?_,fun i j p _ _ _=>?_⟩⟩ <;> simp only [zero_mul,sub_self] <;> exact w_zero
lemma restrict (h:Spent D x ζ M l' S H R)(ht:∀ V,Living x M D V ζ→ ∀ b≥0,H' V b→ H V b): Spent D x ζ M l' S H' R:=by obtain ⟨b,hb,h⟩:=h; exact ⟨b,hb,fun V hv c hc H' => h V hv c hc (ht V hv c hc H')⟩
lemma add (h:Spent D x ζ M l' S H R)(he:Spent D x ζ M l' S H W): Spent D x ζ M l' S H (fun p V=> R p V+W p V):= by obtain ⟨a,ha,h⟩:=h; obtain ⟨c,hc,he⟩:=he; refine ⟨a+c,add_nonneg ha hc,fun V hv b hb g=> ?_⟩; obtain ⟨h,hP⟩:=h V hv b hb g; obtain ⟨ht,hT⟩:=he V hv b hb g; exact ⟨fun i hi=> by simp_rw [add_mul]; exact w_add (h i hi) (ht i hi), fun i j u hi hj hu=> by simp_rw [add_sub_add_comm (R _ _),add_mul]; exact w_add (hP i j u hi hj hu) (hT i j u hi hj hu) ⟩
lemma total (s:Finset X)(K:X→Word→Sketch G→Ribbon (Dye G) k)(h:∀ i∈s,Spent D x ζ M l' S H (K i)): Spent D x ζ M l' S H (fun p v=>∑ i∈s,K i p v):= by induction s using Finset.induction with|empty=>simp only [sum_empty]; apply zero|insert i p hi ih=> simp only [sum_insert hi]; exact add (h i (mem_insert_self ..)) (ih fun i hi=>h i (mem_insert_of_mem hi))
lemma scale {y: Word→ℝ} (h:Spent D x ζ M l' S H R)(he:Backs S y): Spent D x ζ M l' S H (fun p v=> y p • R p v):= by
   obtain ⟨a,ha,h⟩:=h; obtain ⟨⟨p,hp,P⟩,q,hq,Q⟩:=he; let A:=p*a; let W:=A+q*a; have hx:0≤ A:=mul_nonneg hp ha; have hw:A≤ W:=le_add_of_nonneg_right (mul_nonneg hq ha); refine ⟨W,hx.trans hw,fun V hv b hb H=>?_⟩; obtain ⟨h,hV⟩:=h V hv b hb H; constructor
   · intro i hi; apply w_raise (w_scale (h i hi) (y i)); exact le_trans (((mul_le_mul_of_nonneg_right (P i hi) (mul_nonneg ha hb))).trans_eq ((mul_assoc ..).symm)) (mul_le_mul_of_nonneg_right hw hb)
   intro i j u hi hj hk; let n:=u++i; let m:=u++j; let f:=mileage u; let D':=a*b*f; have hd:=mul_nonneg (mul_nonneg ha hb) (mileage_pos u).le; change Weight (y n • R n V-y m • R m V) D l' x _; rw [show y n • R n V-y m • R m V=y n • (R n V-R m V)+(y n-y m) • R m V from by rw [smul_sub,sub_smul]; abel]
   apply w_raise (w_add (w_scale (hV i j u hi hj hk) (y n)) (w_scale (h m (hk.append hj)) (y n-y m))); exact (add_le_add (mul_le_mul_of_nonneg_right (P n (hk.append hi)) hd) (mul_le_mul_of_nonneg_right (Q i j u hi hj hk) (mul_nonneg ha hb))).trans_eq (by unfold W A; ring)
lemma smul (h:Spent D x ζ M l' S H R)(a:ℝ): Spent D x ζ M l' S H (fun p v=>a • R p v):= scale (y:=fun _=>a) h (Backs.given _)
lemma sub (h:Spent D x ζ M l' S H R)(hp:Spent D x ζ M l' S H W): Spent D x ζ M l' S H (fun p v=> R p v-W p v) := by simpa only [neg_one_smul,← sub_eq_add_neg] using add h (smul hp (-1))
end Spent
section beacon
variable {D':ℕ}(hh:enough (e.floorGoal 3 D') S){r k B i:ℕ}
-- apply previously proved joint bounds to all cards of an element
local notation "η" => 2*ζ
local notation "Γ" => terrain ζ (Dye G)
local notation "Υ" => terrain η (Dye G)
abbrev lum (s:Parcel.Step)(e:Parcel G)(p:Word)(z:Cover)(B i n r k:ℕ)(F: Sketch G)(v:E4)(φ:Cards):= beckon e p s z B i (F (Cards.onRoute v (s.L.val:ℝ)⁻¹ φ) n r) k
include T hh hs
omit T hs hh
lemma restMul {Y:Type}{Q: Pulse.Range (Node Y)}{F:Field (Fin k) (Node (Dye G))}(K:Field (Fin k) (Node (Dye G))→Field ι (Node Y))[Fintype ι]{y: Node Y}(hf: Rest Γ (0,x) F b)(he:∀ F:Field (Fin k) (Node (Dye G)),Rest Γ (0,x) F 1→ Poem F→ Rest Q y (K F) c)(w:∀ G d,Rest Γ (0,x) G d→ Poem G→ ∀ a:ℝ, K (a • G)=a • K G)(hp:Poem F): Rest Q y (K F) (c*b):= by -- T etc omit
   rcases hf.cash.eq_or_lt with hb|hb
   · rw [←hb, mul_zero,show F=0 from funext fun i=> norm_le_zero_iff.mp (hb ▸ (budget_single hf.raw i) :‖F i‖≤0 ),show K 0=0 from (by simpa only [zero_smul] using w _ 0 Rest.zero (show Poem (0:Field (Fin k) (Node (Dye G))) from Poem.empty) 0)]; exact Rest.zero
   let a:=b⁻¹ • F; have hA :Rest Γ (0,x) a 1:= (hf.smul _).ist (by rw [Real.norm_of_nonneg (by positivity:b⁻¹≥0),inv_mul_cancel₀ hb.ne']); rw [show K F=b • K a from show _=_ from (w a _ hA (hp.scale _) b|>.symm.trans (congr_arg K (smul_inv_smul₀ hb.ne' F))).symm]; exact ((he a hA (hp.scale _)).smul b).ist (by rw [Real.norm_of_nonneg hb.le, mul_comm])
include T hs hh
lemma beacon (x:Dye G) (d k n:ℕ)(hi:i<B)(hk:k≤B)(hB:B+i≤D')(v:E4)(ht:‖v‖+(s.L.val:ℝ)⁻¹*4≤4)(z:Cover) : Spent D x ζ M Υ S (fun V b=> Enroll Γ D x V d k b) (fun p F=> lum s e p z B i d k n F v):= by
   let X:= Field (Fin k) (Node (Dye G)); let KindArchive:Type:= { F: X // Rest Γ (0,x) F 1}; obtain ⟨⟨b,hb,h⟩,c,hc,H⟩:= momentR T hs hh (F:=fun i:KindArchive=>i.val) (fun p=>p.2) z i n hB; let a:= max b c; let Q p (F:X):= beckon e p s z B i F n; have he (p:Word)(hp:OK S p)(F:X)(d)(ht:Rest Γ (0,x) F d)(h:Poem F)(a:ℝ) : Q p (a • F)= a • Q p F:= by obtain ⟨e',f,t,hT⟩:= permits e p s T hp hs; exact congr_fun (Theater.spot_smul hT (step_reserved s ζ) ht h hi hk a z) n
   refine ⟨a,hb.trans (le_max_left ..), fun V hv p hP hp=> ?_⟩; let f:= Cards.onRoute v (s.L.val:ℝ)⁻¹; have hF(q:Cards)(d':ℝ)(hb:0≤d')(h':Costs D q d'): Rest Γ (0,x) (V (f q) d k) (p*d'):= hp (f q) d' hb (Port.nest_card ht q h' hb); have hu(q:Cards): Poem (V (f q) d k):= (universal (hv.lineage (f q))).incarnate.sym _ _ -- maybe .. inserts all
   constructor
   · intro i hi φ g hg hG; refine (restMul (c:=b) (Q i) (hF φ g hg hG) (fun q hr _=> h i hi (show KindArchive from ⟨q,hr⟩)) (he i hi) (hu φ)).ist ?_ -- K missing
     exact (mul_le_mul_of_nonneg_right (le_max_left b c) (mul_nonneg hP hg)).trans_eq ((mul_assoc ..).symm)
   intro i j u hi hj hk φ g hg hG
   let N:=u++i; let m:=u++j; let K:= fun x':X=> Q N x' - Q m x'; let Z:=c*mileage u; have hz(e:ℝ)(V:X)(hL:Rest Γ (0,x) V e)(hP:Poem V)(v:ℝ) : K (v • V)= v • K V:= by unfold K; rw [he N (hk.append hi) V e hL hP,he m (hk.append hj) V e hL hP,smul_sub]
   refine (restMul (c:=Z) K (hF φ g hg hG) (fun i' h' _=> H i j u hi hj hk (show KindArchive from ⟨i',h'⟩)) (fun V e=> hz e V) (hu φ)).ist ?_; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right b c) (mileage_pos _).le) (mul_nonneg hP hg)) (le_of_eq ?_); unfold a; ring
end beacon
end Transfer
end
end YM.Contacts.Harrier
