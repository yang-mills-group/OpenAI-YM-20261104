import YM.MS.Lifting.Span
import YangMills.WilsonProof.NativeSupport.YM.MS.Lifting.Brand
/-!
# Marking certificates

For local space 'Allowed' and Lease: certificates realtime compact-color moment sums
of finite monomial expressions. Handled wordwise including rank zero. Could use common
cohom choices but not needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Local Local.BV Woven Landau Detect Detect.Mark MeasureTheory Submodule
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G:Gauge}{n:ℕ} {F H:Law G} {b:Bool}
lemma coin_hit : Koszul.coin (A:=Lane4 G) (1:ℂ) = hit:= by ext l; cases l <;> simp [Koszul.coin]
lemma rankC (u:G.El)(n:ℕ)(F:Fin n→Law G): repeatC u (glow (sense G) n F)=glow (sense G) n (repeatC u ∘ F):= by
   induction n with
   | zero=> rw [glow_zero,coin_hit,advance_nil,glow_zero,coin_hit]
   | succ n ih=> rw [glow_add,linkC,ih]; rfl
lemma rankO (n:ℕ)(F:Fin n→Law G): overC (glow (sense G) n F)=glow (sense G) n (overC ∘ F):= by
   induction n with
   | zero=> rw [glow_zero,coin_hit,glow_zero,coin_hit]; exact over_line (n:=0) (fun _=>0)
   | succ n ih=> rw [glow_add,over_p,ih]; rfl

def family (n:ℕ) (f: Fin n→ (CI G) →Grade G) (c:Grid G n):= glow (sense G) n (fun i=> Koszul.mono (f i (c i)))
lemma prodty (n:ℕ) (F:Fin n→Law G): glow (sense G) n F= prodS ℂ (product (sense G)) (coin 1) n F:= by
   induction n with | zero=>rfl| succ n ih=> rw [glow_add,ih]; rfl
private def ML: (Grade G)→ₗ[ℂ] Law G:= ⟨⟨Koszul.mono,Koszul.mlin⟩,fun i f=> Koszul.mcost f i⟩ -- edit
lemma RankColor (n:ℕ)(f: Fin n→ (CI G)→Grade G)(c:Grid G n)(j:G.El)(h:∀ i k, advance j (f i k)=∑ l, wc j l k • f i l): repeatC j (family n f c)=∑ k, (ink j k c:ℂ) • family n f k:= by
    let Z i k: Law G:=Koszul.mono (f i k); have he i: repeatC j (Z i (c i))=∑ l, wc j l (c i) • Z i l:= by
        have hx : repeatC j (Z i (c i)) = ML (advance j (f i (c i))):= by unfold Z ML; change _=Koszul.mono _; rw [ticket,ticket,advance_bud,advance_nil]
        rw [hx,h i (c i),map_sum]; apply Finset.sum_congr rfl; intro l _; exact map_smul ML _ _
    unfold family; change repeatC j (glow (sense G) n (fun i=>Z i (c i)))=_; rw [rankC]; simp_rw [Function.comp_def,he,prodty]; exact color_expand (product (sense G)) _ n Z j c

def breeze (f: Grid G n→ Law G)(j:Grid G n): Law G:= ∑ k, (group G k j:ℂ) • f k
lemma mean_mid (f: Fin n→ (CI G)→ Grade G)(c:Grid G n)(h:∀ i u k, advance u (f i k)=∑ l, wc u l k • f i l): mean (family n f c)= breeze (family n f) c:= by
    ext w; rw [mean_def]; simp_rw [RankColor n f c _ (fun i k=> h i _ k), Finset.sum_apply, Pi.smul_apply,← show ∀ (x:ℝ)(s:ℂ), x•s=(x:ℂ) • s from fun _ _=>rfl]; rw [integral_finsetSum _ ?_]; simp_rw [integral_smul_const,breeze,Finset.sum_apply]; rfl
    intro k _; exact (massInk k c).smul_const _
lemma cloakF (f: Fin n→ (CI G)→ Grade G)(c:Grid G n) (h:∀ i k, over (f i k)=f i k): overC (breeze (family n f) c)=breeze (family n f) c:= by simp_rw [breeze,map_sum,map_smulₛₗ,family,rankO,Function.comp_def,overM,h]; simp

-- invariant *real* span of products; pre-type Language
variable {A:Type}{v q:ℤ}
def phrases (e g:A→ℤ) (f:A→CI G→Grade G)(v b:ℤ)(n:ℕ): Set (Law G):={F|∃ (a:Fin n→ A) (c:Grid G n), (∑ i,e (a i))=v ∧(∑ i,g (a i))=b ∧ F=breeze (family n (f∘a)) c}
lemma syntaxP (X: Set (Law G)) (Hp:∀ f∈X,overC f=f) (h: F∈ Submodule.span ℂ X) : pale F∈ Submodule.span ℝ X:= by
   let C:=Submodule.span ℝ X
   suffices He:∀ x:ℂ,pale (x • F)∈ C by simpa using He 1
   refine span_induction (p:=fun u _=> ∀ x:ℂ,pale (x • u)∈ C) ?_ ?_ ?_ ?_ h
   · intro f hf x; rw [pale,map_smulₛₗ,Hp f hf,←add_smul,show x + starRingEnd ℂ x= (↑(2*x.re):ℂ) from Complex.add_conj x,Complex.ofReal_mul, Complex.ofReal_ofNat,mul_smul, inv_smul_smul₀ (by norm_num :(2:ℂ)≠0)]; exact Submodule.smul_mem C x.re (subset_span hf)
   · intro; simp [pale]
   · intro f g H' K' H K i; convert Submodule.add_mem C (H i) (K i) using 1; simp only [pale,smul_add,map_add]; abel
   intro f g H H' x; rw [smul_smul]; exact H' _
lemma syntaxOk (e g:A→ℤ)(f:A→CI G→Grade G) (H:Bright F)(X:ℤ→ℤ→Set (Grade G)) (hx:F∈ capped FourP X n v q Landau.parity)(hf:∀ v q, ∀ F∈X v q, ∃ l c, e l=v∧g l=q∧ F=f l c)(hu:∀ a c u, advance u (f a c)=∑ l,wc u l c • f a l)(hr:∀ a c, over (f a c)= f a c): F∈ Submodule.span ℝ (phrases e g f v q n):= by
   let J:=phrases e g f v q n; have he: F∈span ℂ J:= by
       rw [← mean_identity (F:=F) H.color]
       suffices he: capped FourP X n v q Landau.parity ≤ Submodule.comap mean (span ℂ J) from he hx
       rw [capped,span_le]; rintro p ⟨α,β,y,hy,rfl,rfl,rfl⟩; choose l t hL hT he using fun i=> hf _ _ _ (hy i); rw [SetLike.mem_coe,Submodule.mem_comap,show glow _ _ _=family n (f∘l) t from by unfold family; simp_rw [Function.comp_apply,he],mean_mid (f∘l) _ (fun i u c=>hu (l i) c u)]; exact subset_span (mem_setOf.mpr ⟨l,t,by simp [hL],by simp [hT],rfl⟩)
   have ht: overC F=F:= H.shadow
   rw [← pale_identity ht]; exact syntaxP _ (fun p h=>by obtain ⟨a,c,H,H',rfl⟩:=h; exact cloakF _ _ (fun i c=> hr (a i) c)) he

lemma rerank (h:F∈ Bed G v q n) : rank n F:= fun i h'=> (tileCub.mp h).rank i (by rw [mod_int] at h'; omega)
-- Lower class
open Physical
lemma syntaxL (H:F∈Lease G v n q): F∈ Submodule.span ℝ (phrases Letter.edge Letter.charge Letter.mark (v-q) q n):=by
   obtain ⟨H,H'⟩:= (byGuide _).mp H; refine syntaxOk _ _ _ H' Loose ?_ (fun v b f H=>H) (fun a c u=> a.weight u c) (fun a c=> a.cloak c);
   refine registred _ H'.weight (rerank H) ?_
   change F∈ Submodule.comap (fac (field Landau.parity) n) (capped FourP (Loose (G:=G)) n (v-q) q Landau.parity)
   refine bed_le _ ?_ H; intro f u s H hu hs ht; rw [Submodule.mem_comap, fac_line, ← hu,← hs]; exact register_span Loose n u s f (fun i=> includeL (H i))
lemma syntaxK (H:F∈Allowed G v n): F∈ Submodule.span ℝ (phrases Plaq.value (fun _=>0) Plaq.mark v 0 n):= by
   obtain ⟨H,H'⟩:= byGuide _ |>.mp H; refine syntaxOk _ _ _ H' Paths ?_ ?_ (fun a c u=> a.weight c u) (fun a c=> a.cloak c); swap
   · rintro i b f ⟨u,v,h,rfl,rfl⟩; exact ⟨u,v,h,rfl,rfl⟩
   refine registred _ H'.weight (rerank (fare G v n H)) ?_
   change F∈ Submodule.comap (fac (field Landau.parity) n) (capped FourP (Paths (G:=G)) n v 0 Landau.parity)
   refine span_le.mpr ?_ H; rintro F ⟨f,x,hf,hx,rfl⟩; subst v; rw [SetLike.mem_coe,Submodule.mem_comap,fac_line]; simpa using register_span (p:=Landau.parity) Paths n x (fun _=>0) f (fun i=> includeP (hf i))
end YM.MS.Lifting
