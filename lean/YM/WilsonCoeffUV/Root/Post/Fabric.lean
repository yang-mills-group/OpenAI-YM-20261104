import YM.WilsonCoeffUV.Root.Post.Shelf
/-!
# Post-price for every strict event. e-column x-rank one layer.
Includes important SLOT fees through ratio.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{U V E:Type*}{r h D l j e k a m t:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X B C δ:ℝ}
-- Foot lamp charges ANOTHER width spectrum. s bounded by Gear.σ for strict κ stack (nongains). slotSmooth pre demand.
structure Bulb (G:Gauge) where
   path: Gear G
   input : ℝ
   s:ℝ
   exitS :ℝ
   preD :ℝ
   dept : 0≤ preD
   inlet :0< input
   positive : 0<exitS
   vio: exitS<s
   outlet :s≤path.σ
   ports : s/path.patch.L.val≤ input
structure Tand (I:Bulb G)(e r D:ℕ) where
   P : Rally (e+1) 0 I.path
   Y : Single G D
   Z : Single G D
   rent i j: lowerGrade i j e r → Shelf Bank.terrain 0 I.input P.x P.σ (Y i j) (Z i j)

variable {I:Bulb G}
namespace Tand
abbrev x (T:Tand I e r D):= T.P.x
abbrev σ (T:Tand I e r D):= T.P.σ
abbrev wealth (T:Tand I e r D):= T.P.rich
end Tand

def Fabric {I:Type*}{J:I→Type*}{α:I→Type*}[NormedAddCommGroup V](x θ:(i:I)→J i→ℝ)(s:I→ℝ)(F P:(i:I)→J i→ Ten V (Cloth (α i)) k) : Prop:= ∃ d:ℕ,∀ i,∃ C:ℝ,0≤ C∧∀ j,Shelf Bank.terrain 0 (s i) (C*x i j^d) (θ i j) (F i j) (P i j)
-- library
section
variable [NormedAddCommGroup V]{I:Type*}{J:I→Type*}{α β:I→Type*}{x θ:(i:I)→J i→ℝ}{s t:I→ℝ}
variable {F P A B:(i:I)→J i→ Ten V (Cloth (α i)) k}
lemma Fabric.add (h:Fabric x θ s F P)(g:Fabric x θ s A B)(hv:∀ i,Brite (x i) (θ i)): Fabric x θ s (F+A) (P+B):=by
    obtain ⟨d,H⟩:=h; obtain ⟨e,T⟩:= g; refine ⟨d+e,fun i=>?_⟩; obtain ⟨A,h,H⟩:= H i; obtain ⟨c,hc,hf⟩:= T i
    exact ⟨A+c,add_nonneg h hc,fun v=> ((H v).add (hf v)).step (roof_pair _ _ _ ((hv i).large _) h hc _ _) ((hv i).dist _)⟩
lemma Fabric.zero :Fabric x θ s (0:(i:I)→J i→ Ten V (Cloth (α i)) k) 0:= ⟨0,fun i=>⟨0,le_rfl, fun j=> by rw [zero_mul]; exact Shelf.zero⟩⟩
lemma Fabric.sum {F P: U→ (i:I)→J i→ Ten V (Cloth (α i)) k}(e:∀ i,Brite (x i) (θ i))(S:Finset U)(p:∀ i∈ S,Fabric x θ s (F i) (P i)): Fabric x θ s (fun i j=>∑ b∈S,F b i j) (fun i j=>∑ b∈S,P b i j):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Fabric.zero
    | @insert i S h ih=> simp_rw [Finset.sum_insert h]; exact (p i (Finset.mem_insert_self ..)).add (ih fun i hi=>p i (Finset.mem_insert_of_mem hi)) e
lemma Fabric.scoopV {F P:(i:I)→J i→ Ten V (Cloth (α i⊕β i)) k}(p:Fabric x θ s F P): Fabric x θ s (fun i j=> scoop (F i j)) (fun i j=> scoop (P i j)):=by
    obtain ⟨d,H⟩:=p; refine ⟨d,fun i=>?_⟩; obtain ⟨a,h,e⟩:= H i; exact ⟨a,h,fun i=> (e i).gulp⟩
variable [NormedSpace ℝ V]
lemma Fabric.mag {f g:(i:I)→J i→ℝ}(u:Bank.Slate x θ f g) (p:Fabric x θ s F P): Fabric x θ s (fun i j=> f i j • F i j) (fun i j=> g i j • P i j):=by
    obtain ⟨d,H⟩:=p; obtain ⟨n,T⟩:=u; refine ⟨d+n,fun i=>?_⟩; obtain ⟨A,h,G⟩:= H i; obtain ⟨B,t,v⟩:= T i
    refine ⟨2*A*B,by positivity,fun j=>?_⟩; rw [pow_add,show 2*A*B*_= 2*(A*x i j^d)*(B*x i j^n) by ring]; exact (G j).mag (v j)
end

-- pick arbitrary point without exponent dependence on dimension.
abbrev Etch (I:Bulb G)(e r D:ℕ):= Tand I e r D × Site I.path.patch.L
abbrev ink (e r D:ℕ)(I:Bulb G)(v: Etch I e r D):= v.1.x
abbrev dye (e r D:ℕ)(I:Bulb G)(v: Etch I e r D):= v.1.σ
lemma welling (e r D:ℕ)(I:Bulb G): Brite (ink e r D I) (dye e r D I):= ⟨fun i=>i.1.P.rich,fun i=> i.1.P.θ⟩
lemma matur (e r D:ℕ)(I:Bulb G): Brite (Tand.x (I:=I) (e:=e) (r:=r) (D:=D)) Tand.σ:= ⟨fun i=>i.P.rich,fun i=>i.P.θ⟩
lemma BankT {α:Type*}{x y:ropes Cover α α}(h:Ballast s C δ x y): Ballast s C δ x.transpose y.transpose:=by
    have hv {x:ropes Cover α α}{C:ℝ}(h:dragCup Bank.terrain s C x):dragCup Bank.terrain s C x.transpose:= by refine ⟨h.1,fun i j=>?_⟩; rw [Bank.terrain.swap]; exact h.2 ..
    exact ⟨hv h.oneP,hv h.otherP,hv h.between⟩
lemma pays_feather {Y Z:ChamberTen G (Vote D) r} (P:Patch)(w:Site P.L)(p:Shelf Bank.terrain 0 s A δ Y Z): Shelf Bank.terrain (lift w) s A δ (featherS P w Y) (featherS P w Z):=by
    let L:= soprano P w D; have hx {A:ℝ}{Y:ChamberTen G (Vote D) r}(p:Cork Bank.terrain 0 s A Y): Cork Bank.terrain (lift w) s A (featherS P w Y):= ((p.turn _).touch L).cost (mul_le_of_le_one_left p.1 (budgetS ..))
    refine ⟨hx p.wax,hx p.wane,?_⟩; rw [show featherS _ _ Y-featherS _ _ Z=featherS P w (Y-Z) from funext fun i=> Eq.symm (map_sub L _ _)]; exact hx p.toll
abbrev ent (e k D j m:ℕ)(I:Bulb G)(v:Etch I e k D):=awning I.path v.1.P.P v.1.Y v.2 j m
abbrev exitC (e k D j m:ℕ)(I:Bulb G)(v:Etch I e k D):=awning I.path v.1.P.Q v.1.Z v.2 j m
variable {π μ: Bulb G→ℝ}
lemma soleFly {P Q:(I:Bulb G)→ Etch I e k D→ ropes Cover (Helms I.path) (Helms I.path)} (p:∀ I,0≤π I)(g:∀ I,π I< μ I)(hz:∀ I,μ I<I.s)(h:∀ i j,Ballast (μ i) i.path.D j.1.σ (P i j) (Q i j))(h₀:m≤ e)
 (H:∀ i≤ t,∀ q<m,∀ j, Fabric (ink e k D) (dye e k D) μ (fun I v=>ent _ _ _ i q I v j) (fun I v=>exitC _ _ _ i q I v j)) (r:ℕ): Fabric (ink e k D) (dye e k D) π (fun I v=> paintC (P I v) v.1.P.P.rays (awning I.path v.1.P.P v.1.Y v.2) t m r) (fun I v=> paintC (Q I v) v.1.P.Q.rays (awning I.path v.1.P.Q v.1.Z v.2) t m r):=by
   simp_rw [paintC,Finset.sum_apply]; apply Fabric.sum (welling (G:=G) e k D); intro i hi; apply Fabric.sum (welling (G:=G) e k D); intro j hj
   have ht:= Finset.mem_antidiagonal.mp hi; have he:= Finset.mem_antidiagonal.mp hj
   simp_rw [rondel]; apply Fabric.sum (welling (G:=G) e k D); intro x hx; have hv:= Finset.mem_antidiagonal.mp hx
   by_cases hh:j.1=0
   · have H (I:Gear G)(M)(T:Stand I)(Y:Gen (Vote D) (Cloth (Helms I))): ruins (swivel (rill M (T.rays i.1 j.1) Y r x.1 x.2))=0:=by
        rw [hh,show T.rays i.1 0=0 from T.negative _]; funext v; unfold ruins swivel; simp_rw [Pi.smul_apply,Finset.sum_apply];
        obtain ⟨l,k⟩:= x; change l+k=r at hv; subst r; simp_rw [rill_spell]; simp
     simp_rw [H]; exact Fabric.zero
   obtain ⟨d,T⟩:= Satin.flywheel (G:=G) i.1 j.1 (x.1+1) (e+1) 0 (Or.inl (by omega)) Gear.σ Gear.holds (fun I=> I.price.le)
   obtain ⟨c,F⟩:= H i.2 (by omega) j.2 (by omega) (x.2+1); refine ⟨d+c,fun I=>?_⟩
   obtain ⟨A,hA,f⟩:= T I.path; obtain ⟨B,hB,s⟩:= F I
   let C:= I.path.D; let Z:= tiePay (Helms I.path) 2 (μ I-π I); let z:= pegPrice x.1 x.2
   have ht:0≤ C:= zero_le_one.trans I.path.bill_nn; have hv':0≤ z:=by unfold z pegPrice; positivity
   have he' : 0≤Z:= tie_nn (sub_pos.mpr (g _)) _
   refine ⟨3*z*C*A*B*Z,by positivity,fun j'=>?_⟩
   have hy:= Shelf.rondelTap (U:=ent _ _ _ i.2 j.2 I j') (T:=exitC _ _ _ i.2 j.2 I j') ((f j'.1.P).graded (le_refl _) ((hz I).le.trans I.outlet)) (s j') (h I j') (g I) (p I) hv
   rw [pow_add]; convert! hy using 1; ring
lemma centuries (e k D m t j:ℕ)(h: m< e ∨ m=e ∧ k< j +2*t) (π:Bulb G→ℝ)(p:∀ I,0≤π I)(g:∀ I,π I < I.s): Fabric (ink e k D) (dye e k D) π (fun I v=> ent _ _ _ t m I v j) (fun I v=> exitC _ _ _ t m I v j):=by
    induction t using Nat.strong_induction_on generalizing m j π with
    | h n ih=>
      cases n with
      | zero=>
        refine ⟨1,fun i=>?_⟩; let U:= i.path; let L:= i.path.patch.L; let T:=tiePay (Pick U) j (i.s-π i); have hs:0< i.s:=i.positive.trans i.vio
        have he:=zero_le_one.trans U.bill_nn; have hT:0≤T:= tie_nn (sub_pos.mpr (g _)) _
        refine ⟨(j+1:ℕ)*U.D^j*Real.exp (8*i.s)*T,by positivity,fun z=>?_⟩; have hx:= z.1.rent m j (by unfold lowerGrade; simpa only [mul_zero, add_zero] using h)
        have ht:= (pays_feather U.patch z.2 hx).portal i.ports hs.le; have hf:= (votes U z.1.P).mono (i.outlet.trans i.path.holds.le)
        simp only [ent,exitC,awning,puck,level, slidesJ]
        have hg :=Shelf.prismLens (P:=tiles L (gatherT U.patch z.2 (lift z.2) z.1.Y m)) (Q:=tiles L (gatherT U.patch z.2 (lift z.2) z.1.Z m)) ht hf (g i) (p i)
        convert! hg using 1; ring
      | succ n=>
        let μ (i:Bulb G):= π i+(i.s-π i)/2
        have hx i:π i<μ i:= by unfold μ; linarith [g i]
        have he i:μ i< i.s:= by unfold μ; linarith [g i]
        have hm (i:Bulb G)(y:Etch i e k D):= (pm_rate y.1.P).mono (show μ i≤ i.path.s from ((he i).le.trans i.outlet).trans i.path.holds.le)
        have hy i: 0≤ μ i:= (p i).trans (hx i).le
        have ht (P Q:(i:Bulb G)→ Etch i e k D → ropes Cover (Helms i.path) (Helms i.path))(v:∀ i j,Ballast (μ i) i.path.D j.1.σ (P i j) (Q i j)):= @soleFly _ _ _ _ _ G π μ P Q p hx he v (show m≤ e from by omega) (show ∀ i≤ n,∀ u<m,∀ j,Fabric .. from fun v hv u hu j=> ih v (by omega) u j (Or.inl (by omega)) μ hy he) j
        have hb: Fabric (ink e k D) (dye e k D) π (fun I v=> rime v.1.P.P.payMat (ent _ _ _ n m I v) j) (fun I v=> rime v.1.P.Q.payMat (exitC _ _ _ n m I v) j):=by
           obtain ⟨d,H⟩:= ih n n.lt_succ_self m (j+2) (by omega) μ hy he; refine ⟨d,fun I=>?_⟩; obtain ⟨A,hA,f⟩:= H I
           let T:=tiePay (Helms I.path) 2 (μ I-π I); have hT : 0≤ T:= tie_nn (sub_pos.mpr (hx I)) _
           have hu:0≤fareV j:= by unfold fareV; positivity
           have hk:= zero_le_one.trans I.path.bill_nn
           refine ⟨2*I.path.D*A*fareV j*T,by positivity,fun v=>?_⟩
           convert! Shelf.rimming (P:=ent _ _ _ n m I v) (Q:=exitC _ _ _ n m I v) (f v) (hm I v) (hx I) (p I) using 1; ring
        simp_rw [ent,exitC,awning,puck,inchC,Pi.smul_apply, Pi.add_apply]; apply Fabric.mag (Bank.Slate.one (P:=fun _=>((n+1:ℕ):ℝ)⁻¹) (welling (G:=G) e k D)); exact ((hb.add (ht _ _ hm) (welling (G:=G) e k D)).add (ht _ _ (fun i j=> BankT (hm i j))) (welling (G:=G) e k D))
end YM.WilsonCoeffUV.Cosmos
