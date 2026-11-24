import YM.X.Rank.Middle
/-! Silence against local color-quadratic probes implies silence against the
bilocal probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {a b m d v u : E4}(c : G.ColorIndex) {P: Canvas G}
def loci (W : List Scout) := (W.map Prod.fst).toFinset
def adm (S:Finset E4) (W : List Scout): Prop:= (W.map Prod.fst).Nodup ∧ Disjoint (loci W) S
def clothe (W:List Scout) : Canvas G:= (W.map (fun w=>patch w w)).prod
def Silent (P:Canvas G)(S:Finset E4): Prop:=∀ W, adm S W → E c (clothe W * P)=0
@[simp] lemma loci_cons (a:Scout)(W:List Scout):loci (a::W)=insert a.1 (loci W):= by simp [loci]
@[simp] lemma clothe_cons (a:Scout)(W:List Scout):clothe (G:=G) (a::W)=patch a a*clothe W:= rfl
lemma adm_cons (a:Scout)(W:List Scout): adm S (a::W) ↔ a.1∉ S ∧ a.1∉ loci W ∧ adm S W:= by
  simp only [adm,List.map_cons,List.nodup_cons,loci_cons,Finset.disjoint_insert_left]
  simp only [loci,List.mem_toFinset]; tauto
lemma wear_fits (W:List Scout)(h:∀ i∈ loci W,i∈S) : Fits (S:Set E4) (clothe W:Canvas G) := by
  let s:=supported ℂ {i:Fiber G| i.1.1∈S}; induction W with
  | nil=> exact s.one_mem
  | cons a L ih=>
    apply s.mul_mem _ (ih fun i hi=> h i (loci_cons a L|>.symm ▸ Finset.mem_insert_of_mem hi)); exact patch_supported a a _ (fun i k=> h _ (by simp)) (fun i k=>h _ (by simp))
lemma Fits.incl {P:Canvas G}{S T : Finset E4}(h: Fits (S:Set E4) P)(ht:S⊆T): Fits (T:Set E4) P := by
    rw [Fits,mem_supported] at *; exact fun i hi=> ht (h hi)
section strike
variable (hp:Fits (S:Set E4) P)(he:Silent c P S) (ha:a∉S)(hb:b∉S)(hx:a≠b)
private lemma go_dark (hh:View S a b m d v) (w:Flavor 0)(f:Stroke→ℂ)(hH:∀ i:Stroke,MidOK S a b i→ Shine (shining c m d v w i) (f i))
    {y:E4}(hk:u=a∨u=b)(ht:u-m=y) -- y implicit add
    (hz : Rad.beam y v=Rad.beam d v) {x:ℂ}(h₀:Shine (fun t:ℝ=> glint y v t*fare c w w (y+t • v)) x): bill u w f=x:= by
  have hi:= scaled_bill c m d v w f (u,w) fun i=>hH (shell u i) (Or.inr ⟨hk,rfl⟩)
  apply (hi.respects ?_).separates h₀; filter_upwards [beam_nonzero (u:=y) hh.hv] with r hR; change _* hot _ _ _ = _; unfold hot; let t:=r • v; dsimp only [penumbra]; have H:u-(m-t)=y+r•v:= by rw [← ht]; abel
  rw [if_neg (sub_ne_zero.mp (H.symm ▸ hR)),H]; unfold glint; rw [hz]
include hp he ha hb hx
private lemma pole (z x:Flavor 0) (w: Flavor 0)(h:View S a b m d v) (f:Stroke→ℂ)(hT:∀ i:Stroke, i.1∈S→f i=0)(hH:∀ i:Stroke,MidOK S a b i→ Shine (shining c m d v w i) (f i))
    (hA:bill a z f≠0)(hB: bill b x f≠0): E c (patch (a,z) (b,x) * P)=0:= by
  let u:Scout:=(a,z); let y:Scout:=(b,x)
  have hU :∀ p:Scout,p.1∉S→E c (patch p p*P)=0:=fun p ht=>by convert he [p] (by simp [adm,loci,ht]) using 2; simp [clothe]
  refine pole_zero c P hp (z:=u) (z':=y) rfl rfl h w f hT hH hA hB (hU _ ha) (hU _ hb) ?_
  filter_upwards [Rad.clears (v:=-v) (neg_ne_zero.mpr h.hv) m (insert a (insert b S))] with t ht
  have hΩ := show m-t • v ≠ a ∧ m-t • v≠b ∧ m-t • v∉S from (by simpa [sub_eq_add_neg] using ht)
  convert he [penumbra m v w t,u,y] ((adm_cons ..).mpr ⟨hΩ.2.2, (by simp [hΩ.1,hΩ.2.1,loci,u,y]), by simp [adm_cons,u,y,hx,ha,hb]; simp [adm,loci]⟩) using 1
  all_goals simp [clothe,mul_assoc]
omit hp he ha hb hx
lemma by_flavor (a b:E4)(r s t: Flavor 0): patch (G:=G) (a,r+s) (b,t)=patch (a,r) (b,t)+patch (a,s) (b,t) := by
  choose L h using fun i : G.ColorIndex=> torch_linear i a
  simp_rw [patch,h,map_add,add_mul,Finset.sum_add_distrib] -- h binder applied at fixed a; b defin?
private lemma by_mass (f:Flavor 0→ ℂ)(L:Flavor 0 →ₗ[ℝ]ℂ) (w:Flavor 0) (hw:L w≠0)(hf:∀ a b,f (a+b)=f a+f b) (h:∀ p,L p≠0→ f p=0) (p:Flavor 0): f p=0:= by
  by_contra hx; have ht:L p=0:=not_not.mp (fun ht=>hx (h p ht)); have h':= h (p+w) (by rw [map_add,ht,zero_add]; exact hw); rw [hf,h w hw,add_zero] at h';exact hx h'
include hp he ha hb hx
lemma pair_reads (z y:Flavor 0): E c (patch (a,z) (b,y) * P)=0 := by
  obtain ⟨m,d,v,H⟩:= Rad.viewing hx ha hb; obtain ⟨w,x,y',ht,hm,hK,hM⟩:= Rad.hit H.hv H.onBeam c
  obtain ⟨f,hf,hS⟩:=shimmers c H w
  obtain ⟨A,hA⟩:=cash_linear f a; obtain ⟨B,hB⟩:=cash_linear f b
  have e:=(go_dark c H w f hS (Or.inl rfl) H.h₁ rfl hK); have hD:= beam_eq (beam_iff.mp H.onBeam|>.2)
  have E':=(go_dark c H w f hS (Or.inr rfl) H.h₂ hD (x:=y') (by simpa only [glint,hD] using hM))
  apply by_mass (fun z=>E c (patch (a,z) (b,y)*P)) A w ((congr_fun hA w).symm.trans e|>.trans_ne ht) ?_ ?_ z
  · exact fun r s=>by simp only [by_flavor a b,add_mul,map_add]
  intro x h; apply by_mass (fun y=> E c (patch (a,x) (b,y)*P)) B w ((congr_fun hB w).symm.trans E'|>.trans_ne hm) ?_ ?_ y
  · intro r s; simp_rw [fun z : Flavor 0=>patch_comm (G:=G) (a,x) (b,z),by_flavor,add_mul,map_add]
  intro y hy; exact pole c hp he ha hb hx x y w H f hf hS ((congr_fun hA x).trans_ne h) ((congr_fun hB y).trans_ne hy)
end strike
end YM.PositionX.Rank
