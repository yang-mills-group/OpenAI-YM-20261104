import YM.MSbar.Counter.Symbol

/-! Principal Laurent part. **No ζ^0**. Thus an unambiguous global family summand;
no canonically chosen values outside the expansion disk needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Counter
open Dim Symbol Domain Diagram Scale Super Loops Function Set Filter
open scoped Classical Topology BigOperators ContDiff
variable {C:Type} {i m j t:ℕ} {U V:Set ℂ} {W:Edition C}{d:Bit} {f g: Vertex C}{F G:Functionals C}

def winter (f:Vertex C) (F:Functionals C) : Functionals C := fun z=> z⁻¹ • (f+F z)
def Winter (W:Edition C)(d:Bit): ℕ→Functionals C→Prop
    | 0, f => f=0
    | n+1, F => ∃ g f, Winter W d n g ∧ Live W d f ∧ F=winter f g
namespace Winter
lemma empty_free (i:ℕ) : Winter W d i 0:= by
    induction i with
    | zero=>exact rfl
    | succ n ih=> exact ⟨0,0,ih,Live.zero, by funext z; simp [winter]⟩
lemma add (h:Winter W d i F)(H:Winter W d i G): Winter W d i (F+G):= by
    induction i generalizing F G with
    | zero=> simp_all [Winter]
    | succ n ih => obtain ⟨g,f,hg,hf,rfl⟩:=h; obtain ⟨l,r,hl,hr,rfl⟩:=H; exact ⟨g+l,f+r,ih hg hl,Live.add hf hr, funext fun z=>by simp [winter,smul_add]; abel⟩
lemma scale (h:Winter W d i F)(c:ℂ): Winter W d i (c•F):=by
    induction i generalizing F with
    | zero=> simp_all [Winter]
    | succ n ih=> obtain ⟨g,f,hg,hf,rfl⟩:=h; exact ⟨c•g,c•f,ih hg,Live.scale c hf, funext fun z=> by rw [Pi.smul_apply, winter, smul_comm c z⁻¹]; simp [winter,smul_add]⟩
lemma sub (h:Winter W d i F)(H:Winter W d i G): Winter W d i (F-G):=by rw [sub_eq_add_neg]; exact h.add (by simpa only [neg_smul,one_smul] using H.scale (-1:ℂ))
lemma rise (h:Winter W d i F)(he:i≤j): Winter W d j F:= by
    induction i generalizing j F with
    | zero => change F=0 at h; rw [h]; exact empty_free _
    | succ i ih=>obtain ⟨g,f,hg,hf,rfl⟩:=h; cases j with | zero=>omega | succ n=>exact ⟨_,_,ih hg (by omega),hf,rfl⟩
lemma live (h:Winter W d i F)(x:ℂ): Live W d (F x):= by induction i generalizing F with | zero=>change F=0 at h; rw [h]; exact Live.zero | succ i ih=>obtain ⟨g,f,hg,hf,rfl⟩:=h; exact Live.scale _ (Live.add hf (ih hg))
variable [Profit U]
lemma bound (h:Winter W d i F):Price i U W d F:= by
    induction i generalizing F with
    | zero=> change F=0 at h; rw [h]; exact Price.zero
    | succ i ih=> obtain ⟨g,f,hg,hf,rfl⟩:=h; obtain ⟨G,hG,h⟩:= ((Bright.regular (U:=U) (F:=liftV f) (cold hf)).grow (Nat.zero_le i)).add (ih hg)
                  exact ⟨G,hG,fun x hx=> by rw [← h hx,swell_inner,swell_inner,winter,pow_succ,mul_smul,smul_inv_smul₀ (show x≠0 from hx.2)]; rfl⟩
lemma negative (h:Winter W d i F)(hr: Regular U W d F): F=0:= by
    induction i generalizing F with
    | zero=> exact h
    | succ i ih=> obtain ⟨g,f,hg,hf,rfl⟩:=h; obtain ⟨G,hG,H⟩:= Price.rem hr
                  let A:Functionals C:= times id G; have hA:Bright U W d A:= Bright.temp hG differentiableOn_id
                  have he: EqOn (liftV f + g) A (rim U):=fun z hz=>by rw [show A z=z • G z from rfl,← H hz,winter,smul_inv_smul₀ (show z≠0 from hz.2)]; rfl
                  have hu: g=0:= ih hg ⟨A-liftV f,hA.sub (cold hf),fun z hz=> by simp only [bare_swell, Pi.sub_apply,← he hz,Pi.add_apply,add_sub_cancel_left]⟩
                  subst g; have he':EqOn (liftV f) A (rim U):= by simpa using he
                  have hh : f=0:=by
                      have ht:=(Bright.keep (cold hf) he' hA) (Profit.around (U:=U))
                      change f= (0:ℂ) • G 0 at ht; simpa using ht
                  subst f; ext1 z; simp [winter]
end Winter

lemma singular [Profit U] (h:Price i U W d F): ∃ G, Winter W d i G ∧ Regular U W d (F-G):=by
    induction i generalizing F with
    | zero=> exact ⟨0,rfl,by simpa⟩
    | succ i ih=> let H:=times id F; obtain ⟨G,hG,hh⟩ := ih (F:=H) (by obtain ⟨X,hX,h⟩:=h; exact ⟨X,hX,fun z hz=> by rw [← h hz,swell_inner,swell_inner,pow_succ,mul_smul]; rfl⟩);
                  obtain ⟨L,hL,hp⟩:= Price.rem hh; refine ⟨winter (L 0) G, ⟨_,_,hG,hL.freeze Profit.around,rfl⟩, (Bright.regular (Bright.chops hL)).recognize ?_⟩
                  intro z hz; apply smul_right_injective (Vertex C) (show z≠0 from hz.2); dsimp only;  rw [Pi.sub_apply,smul_sub,stripping,winter,smul_inv_smul₀ (show z≠0 from hz.2),← hp hz,Pi.sub_apply]; change _=z • F z-G z- L 0; abel
lemma unique [Profit U] (h: Regular U W d (F-G))(hG:Winter W d i G){K:Functionals C}(hK: Regular U W d (F-K))(hk:Winter W d j K): K=G:=by
    have hl:= (hk.rise (Nat.le_max_left j i)).sub (hG.rise (Nat.le_max_right j i))
    exact sub_eq_zero.mp (hl.negative (show Regular U W d (K-G) by rw [show K-G=(F-G)-(F-K) by abel]; exact Price.sub h hK))
-- Recovery: global Principal independent of degree and pole budget (degree uniqueness later if needed), dependent choice only region.
def principal (W:Edition C)(d:Bit) (U:Set ℂ)(F:Functionals C): Functionals C:=
    if h: ∃ G, (∃ i,Winter W d i G) ∧ Regular U W d (F-G) then h.choose else 0
lemma is_principal [Profit U] (h:Regular U W d (F-G)) (hG:Winter W d i G): principal W d U F= G:= by
    unfold principal; split_ifs with hh
    · obtain ⟨i,H⟩:= hh.choose_spec.1; exact unique h hG hh.choose_spec.2 H
    exact (hh ⟨G,⟨_,hG⟩,h⟩).elim
namespace Price
variable [Profit U]
lemma pair (h: Price i U W d F): Winter W d i (principal W d U F) ∧ Regular U W d (F-principal W d U F):=by obtain ⟨G,hG,H⟩:=singular h; rw [is_principal H hG]; exact ⟨hG,H⟩
lemma criterion (h: Price i U W d F): principal W d U F=0 ↔ Regular U W d F:= by
    refine ⟨fun e=> by simpa [e] using h.pair.2, fun he=> is_principal (by simpa using he) (Winter.empty_free i)⟩
lemma combine (h: Price i U W d F)(H:Price j U W d G): principal W d U (F+G)= principal W d U F+principal W d U G:= by
    obtain ⟨a,b⟩:= (h.grow (Nat.le_max_left i j)).pair; obtain ⟨e,f⟩:= (H.grow (Nat.le_max_right i j)).pair
    apply is_principal _ (a.add e); convert Price.add b f using 1; abel
lemma take (h: Price i U W d F)(c:ℂ): principal W d U (c•F)=c • principal W d U F:= is_principal (by simpa only [smul_sub] using Price.scale h.pair.2 c) (h.pair.1.scale c)
lemma region [Profit V] (h: Price i U W d F)(hn:V⊆U): principal W d V F=principal W d U F:= is_principal (Price.slim h.pair.2 hn) h.pair.1
lemma relative (h:Price i U W d F)(H: EqOn G F (rim U)): principal W d U G=principal W d U F:=
    is_principal (Price.recognize h.pair.2 (fun z hz=> by simp only [Pi.sub_apply,H hz])) h.pair.1
end Price
end YM.MSbar.Counter
