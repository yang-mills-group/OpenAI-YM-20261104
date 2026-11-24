import YM.FVA2.AntiBoot
/-! # continuum MS parity. Tagged positions as in Dial construction. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.MS.Reed
open Filter Topology Set Function MeasureTheory Real Metric
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap Fiddle City Job Geo Land Local.Physical Port Tide Fleet Puff Engine Actors Puff.Mom
open PeakT -- ordZ
open Vane
open Finset
open scoped Topology ContDiff
variable {G:Gauge}{I W:Type}{B:Local.Physical.Deck G}{A:Booked B}(D: MS_Data G A){i:I}{s t:ℝ}{k n m:ℕ}
variable {V: Rake.Dance G I W}{x:Rake.Position W I}{Y: Geo I}{L: W→ Label B}[LinearOrder W]{j u y: Finset W}
local notation "ϵ"=> ϕ (R:=ℂ)
private lemma fuses {T X:Glade G I} {K:Planet G I}(he:T i t=ϵ n • J _ ℂ (T i t))(hV:X i t= ϵ m • J _ ℂ ( X i t)) : expJ K T X i t= (ϵ (n+m)) • J _ ℂ (expJ K T X i t):=by
    unfold expJ; rw [ Reed.joins ]; nth_rw 1 [he,hV]; -- tree smul
    simp only [← blvd,map_smul,LinearMap.smul_apply,ϕ,pow_add,mul_smul ]; exact smul_comm .. -- simpler via Flux.Room. lookup
private lemma cabinF (p:QP)(K:Edge G)(μ:Measure QP)(F H:Law G) (he:F=ϵ n • J _ ℂ F)(hV:H=ϵ m • J _ ℂ H): Cabin p K μ F H= ϵ (n+m) • J _ ℂ (Cabin p K μ F H):= by
    ext l; unfold Cabin; rw [Pi.smul_apply,rite,smul_eq_mul, ← mul_assoc, collectL ]; refine scatter_congr _ _ _ _ (fun i j hij =>?_); unfold meshZ; rw [mul_left_comm (ϵ _ * ϵ _ )]; simp_rw [Finset.mul_sum, ← integral_const_mul ]; apply Finset.sum_congr rfl; intro a ha; apply Finset.sum_congr rfl; intro b hb; congr 1; funext t; let u:= (a,t)::i; let v:=(b,-t)::j;
    nth_rw 1 [congr_fun he u,congr_fun hV v]; simp_rw [Pi.smul_apply,rite, u,v,List.length_cons, ← split_length hij,smul_eq_mul, rite1, ϕ,pow_add ]; ring
variable {D}(hp:DOrd A Y D L x V)
local notation "Δ"=> constantP G I (PlanetD G)
local notation "μ"=> (fun _ : I => planeF)
abbrev rankR (L:W→ Label B)(t:Finset W):= ∑ i∈t,(Land.read ( L i ).item).grade
set_option quotPrecheck false
local notation "Ξ"=> rankR L
private lemma add_r (hu:u⊆ j) : Ξ u+Ξ (j\u)=Ξ j:=by unfold rankR; rw [add_comm]; exact Finset.sum_sdiff hu
-- solve
include hp
lemma dances (i:I)(j:Finset W)(k:ℕ) (t:ℝ): V j k i t= (ϕ (Ξ j+k):ℂ) • J _ ℂ (V j k i t):= by
   induction j using Finset.strongInductionOn generalizing k t with| _ j ih=>
    rcases lt_or_ge j.card 2 with hv|hv
    · obtain h|h:= show j.card=0∨j.card=1 from (by omega)
      · rw [ card_eq_zero.mp h,hp.1 ]; simp
      obtain ⟨s,rfl⟩:= card_eq_one.mp h; rw [hp.2.1 ]; simp only [rankR,sum_singleton,comp_apply,Rake.rowM,Rake.circle,Rake.nameR]; exact sale_archive D (L s).item k _
    induction k using Nat.strong_induction_on generalizing t with| h k hL=>
       obtain ⟨ ⟨a,b⟩,hs,hm⟩:= hp.2.2 j hv k; let r:=Ξ j+k; let P(m):= Domain.paths m 0
       let C:= V j k; let T:= Vane.rhs x μ Δ Δ (approach Y D) V j k; change V j k=river T at hm;
       have he (t:ℝ)(n:ℕ) : approach Y D n i t=(ϕ n:ℂ) • J _ ℂ (approach Y D n i t) := ArchiveJ D n (Y.η i,t)
       let E(n p:ℕ):= expJ Δ (approach Y D p) (V j n); let S:= Src x μ Δ Δ (approach Y D) V j k;
       have Q (t:ℝ): S i t=ϵ r • J _ ℂ ( S i t):= by
           have hO: lonely Δ (approach Y D) (V j) k i t=ϵ r • J _ ℂ (lonely Δ (approach Y D) (V j) k i t):= by
               unfold lonely; simp_rw [Finset.sum_apply,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro n h; have hx:= Finset.mem_Ico.mp h; obtain hl:= fuses (K:=Δ) (he t (k-n)) (hL n hx.2 t); rw [show k-n+(Ξ j+n) = r from by unfold r; omega ] at hl; exact hl
           unfold S Src multi; simp_rw [Pi.add_apply,map_add,smul_add,Finset.sum_apply,map_sum,Finset.smul_sum ]; refine congr_arg₂ (·+·) hO ?_
           apply Finset.sum_congr rfl; intro s hs; apply Finset.sum_congr rfl; intro a ha; unfold regionC; have hy:= n_small hs; have ht : Ξ s+a.1+(Ξ (j \ s)+a.2)=r := (by unfold r; obtain hx:= mem_antidiagonal.mp ha; obtain hv:= add_r (L:=L) (n_small hs|>.1.le); omega); rw [← ht ]; exact cabinF _ _ _ _ _ (ih s hy.1 a.1 t) (ih _ hy.2.2.2 a.2 t)
       let R(u:ℝ)(L: Legs (Lane4 G)):= C i u L; ext l; suffices hx: ∀ (p:ℕ) (t:ℝ) (L: Legs (Lane4 G)), a<p+L.length → R t L= (ϕ r:ℂ) * (ϕ L.length * R t L) from hx (a+1) t l (by omega)
       intro n; induction n with
       | zero=> intro t L h; rw [show R t L=0 from b i t L (by omega),mul_zero,mul_zero ] -- need diversity is strict > ? check
       | succ n hh=>
          intro t l h
          have hV(u:ℝ) : T i u l= (ϵ r)* (ϵ l.length*T i u l):= by
              unfold T rhs; have hl: (sailP μ Δ C) i u l=(ϵ r)* (ϵ l.length* (sailP μ Δ C i u l)):= by
                 unfold sailP cycle; simp_rw [ ← integral_const_mul,at_trc,Finset.mul_sum ]; apply integral_congr_ae; refine Eventually.of_forall fun a => Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl (fun k _=>?_); -- ih pattern
                 obtain ht:= hh u ((j,a)::(k,-a)::l) ( by simp only [List.length_cons]; omega ); simp_rw [List.length_cons,rite1,neg_neg] at ht; -- rewrite F.1 exactly
                 simp_rw [mul_left_comm (ϵ l.length) (Δ i u j k a), mul_left_comm (ϵ r) (Δ i u j k a) ]; exact congr_arg (_ * ·) ht
              have hx: S i u l= (ϵ r)* (ϵ l.length * S i u l):= congr_fun (Q u) l; simp only [Pi.add_apply,mul_add ]; exact congr_arg₂ (·+·) hl hx
          unfold R C; rw [hm ]; unfold river; simp_rw [ ← integral_const_mul ]; exact integral_congr_ae (Eventually.of_forall hV)
-- parity at scalar output along t∞
lemma bladeJ (i:I) (hx:Mesh Y x)(s:Finset W) (n:ℕ) : Vane.blade ( V s n ) i= (ϕ (Ξ s+n):ℂ) * ( Vane.blade ( V s n ) i ):= by
    rcases s.eq_empty_or_nonempty with h|h; · subst s; rw [ hp.1 ]; change Vane.blade (0:Glade G I) i=_*Vane.blade (0:Glade G I) i; rw [(Fleet.allow_zero i).2 ]; -- lookup type
                                                         simp
    obtain H:= ( Dial.reports L hx hp h n|>.1 i ); refine tendsto_nhds_unique H (Tendsto.congr (fun t=>?_) ( H.const_mul _ )); -- names & orient
    obtain hp:= congr_fun ( dances hp i s n t ) []; change V s n i t []=_ *(ϕ (List.length ([]:Legs (Lane4 G))) * _) at hp; simpa [ϕ] using hp.symm
omit hp
lemma book_sign {q:W→QP}(hq:Injective q)(i:Finset W)(n:ℕ): Dial.book D L s q i n= ϵ (Ξ i+n) * Dial.book D L s q i n:= by
   have hu: Rake.Mesh (frameF Unit s) (fun k (_:Unit)=> q k) := by -- specialize repeated
       intro i j hi; have he:0<‖q i-q j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hq.ne hi)); exact ⟨⟨_,he,fun k=>by simp [roots]⟩, _,he,fun k=>by simp [ roots ]⟩
   obtain hV:= Dial.pin D L s hq; exact bladeJ hV () hu i n -- frameF from which ns?
open Puff.Log Puff.SplitP Dial
section
variable {F H:Finset W→T ℂ}
local notation "Πm"=> (Puff.Mom.Trunk.stack (marked W) )
abbrev RootP (L:W→Label B)(F: Finset W → T ℂ) : Prop:= ∀ (i:Finset W)(n:ℕ),F i n=(ϕ (rankR L i+n):ℂ)* F i n
private lemma paint_mul (hf:RootP L F)(hx:RootP L H): RootP L (Πm.core F H):= by
    intro i n; change (∑ d∈subs i,Trunk.core ( F d.1 ) ( H d.2 )) n= _ * ((∑ d∈subs i, Trunk.core ( F d.1 ) ( H d.2 )) n); simp_rw [Finset.sum_apply,Finset.mul_sum ]; apply Finset.sum_congr rfl; rintro ⟨a,b⟩ ha; obtain ⟨h,rfl⟩:= Puff.SplitP.cards.mp ha;
    change ∑ d∈antidiagonal n,F a d.1* H (i\a) d.2= (ϵ (Ξ i+n))*(∑ d∈ antidiagonal n,F a d.1*H ( i \ a ) d.2 ); rw [Finset.mul_sum ]; apply Finset.sum_congr rfl; intro d hd; nth_rw 1 [hf a d.1, hx (i \ a ) d.2]; rw [ show Ξ i+n=Ξ a+d.1+(Ξ (i\a)+d.2) from by obtain he:= add_r (L:=L) h; obtain hz:= mem_antidiagonal.mp hd; omega, ϕ]; rw [pow_add]; unfold ϕ; ring
lemma greetings (h:RootP L F)(k:ℕ): RootP L ( Πm.power F k):= by
    induction k with
    | zero=> intro i n; by_cases hi:i=∅ ∧ n=0; · obtain ⟨rfl,rfl⟩:= hi; rw [ rankR, sum_empty ]; simp only [ϕ,add_zero,pow_zero,one_mul ]; -- both
             rw [ show Πm.power F 0 i n=0 from ?_,mul_zero ]; change (marked W|>.refineV ( SplitP.nat.refineV 1 ) i) n=0; unfold refineV; split; · rename_i h; exact if_neg (fun he=> hi ⟨h,he⟩)
             rfl
    | succ i ih=> exact paint_mul h ih
lemma projection {q: W→QP}(h:Injective q) : RootP L (Dial.tour D L s q):= by
   let X:= Dial.book D L s q; obtain hp: RootP L X:= book_sign h; intro w m; unfold Dial.tour bouquet Cheer Actors.cheers; simp_rw [ Finset.sum_apply,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _;
   have he:= greetings hp j w m; change Puff.Actors.phase j * _= _*( Puff.Actors.phase j * _ ); rw [ mul_left_comm ]; exact congr_arg ( Puff.Actors.phase j*· ) he
end
end YM.MS.Reed
