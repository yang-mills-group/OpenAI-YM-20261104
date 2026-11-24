import YM.MS.City.Bus
/-!
# hypercubic group on tree terms

Work only Cpu. Integral argument preserves ext rotation of scalar via frames.
 Keep general Course true; can use all true for simplicity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect
open Complex (I)
open scoped Topology ContDiff Pointwise
variable {G:Gauge} (s:Signed) {b:Bool}{F H: Landau.Detect.Law G}{l:List (Lane4 G)}{t:ℝ}
abbrev SideS (s:Signed)(l:List (Lane4 G)):ℂ:= (l.map (negateField s)).prod
lemma twice_S (l:List (Lane4 G)): SideS s l*SideS s l=1:= by induction l with| nil=>exact one_mul _ | cons i l ih=> rw [show SideS s (i::l)=tick s i.1 * SideS s l from rfl, mul_mul_mul_comm, ih,tick2,one_mul]
lemma oppositeS (h:SignedScope b F)(hw:Course b l): F (l.map (permute s))= SideS s l*F l:= by rw [← h s l hw,← mul_assoc, show SideS s l * (l.map (negateField s)).prod=1 from twice_S s l,one_mul]
lemma back_p (l: Lane4 G): field parity (permute s l)=field parity l:= by rcases l with ⟨⟨⟨_|a,_|_⟩,i⟩,x⟩ <;> rfl
lemma scat_move (l:List (Lane4 G))(F:Shared (Mode (BH G) QP) ℂ) : scatter (field parity) (l.map (permute s)) F=scatter (field parity) l (fun u v=> F (u.map (permute s)) (v.map (permute s))):= by
    induction l generalizing F with
    | nil=> rfl
    | cons i l ih=> rw [List.map_cons,scatter_cons,ih,scatter_cons]; congr! 2; funext u; rename_i v; simp only [List.map_cons,back_p]
                    have hz (v:List (Lane4 G)): degree (field parity) (v.map (permute s))=degree (field parity) v:= by induction v with| nil=>rfl| cons i v ih=> simp only [List.map_cons,degree_cons,back_p,ih]
                    rw [hz]
lemma radiance (h:SignedScope b F)(hh:SignedScope b H)(l r:List (Lane4 G))(hw:b=true → net l+ net r=0) (i j:BH G):
 radius parity (Cpu G t) (passN s i) (passN s j) F H (l.map (permute s)) (r.map (permute s))= SideS s l*SideS s r* radius parity (Cpu G t) i j F H l r:= by
    have hF: Course b ((i,-net l)::l):= fun _=>by simp
    have hH: Course b ((j,- -net l)::r):= fun hx=>by simp [hw hx]
    have he : degree (field parity) (l.map (permute s))=degree (field parity) l:= by clear hF hH hw; induction l with| nil=>rfl| cons i v ih=> simp only [List.map_cons,degree_cons,back_p,ih]
    unfold radius; rw [he,repose]; dsimp only; rw [← Signed.act_neg,← Signed.act_neg, turn_p,show F ((passN s i,s.act _ )::_)=SideS s ((i,-net l)::l)*F ((i,-net l)::l) from ?_, show H ((passN s j,s.act _ )::_)=SideS s ((j,- -net l)::r)* H ((j,- -net l)::r) from ?_]
    · simp only [SideS,List.map_cons,List.prod_cons,tick1]; rw [show parity ((passN s) j)=parity j from back_p s (j,(0:QP))]; ring_nf; simp only [pow_two, tick2,mul_one,one_mul]
    · simpa only [List.map_cons, passenger] using oppositeS s hh hH
    simpa only [List.map_cons, passenger] using oppositeS s h hF
lemma alight_t {t:ℝ}(h:SignedScope b F)(hh: SignedScope b H): SignedScope b (tree parity (Cpu G t) F H):= by
    intro k w hw; unfold tree; rw [scat_move]; let N:=allocate (field parity) w (R:=ℂ); change SideS k w • N _=N _; rw [← map_smul]; apply (scatter_congr _ _ _ _); intro a b he;
    rw [Pi.smul_apply, Pi.smul_apply, convertR (Vrev G t),convertR (Vrev G t)]; rw [← Equiv.sum_comp (passN k),Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [← Equiv.sum_comp (passN k), Finset.smul_sum]; refine Finset.sum_congr rfl (fun j _=>?_);
    rw [radiance k h hh _ _ (fun q=> (split_net he).trans (hw q)),show SideS k a*SideS k b=SideS k w from by simpa [SideS] using ((split_perm he).map (negateField k)).prod_eq]; rw [smul_eq_mul,← mul_assoc,twice_S,one_mul]
lemma cycle_t {t:ℝ}(h:SignedScope b F) : SignedScope b (Ccy (Cpu G t) F μzone):= by
   intro s l hl; unfold Ccy; let K:=Cpu G t; change SideS s l*(∫ u,trc K u F (l.map (permute s)) ∂μzone)= ∫ u,trc K u F l ∂μzone; rw [← (measureVeh s).integral_comp', ← integral_const_mul];
   refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); dsimp only; rw [at_trc, at_trc,← Equiv.sum_comp (passN s),Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [← Equiv.sum_comp (passN s),Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _=>?_); change SideS s l*(Cpu G t _ _ (s.act x)* F (_::(_, - s.act x)::_))= _;
   have hv:Course b ((i,x)::(j,-x)::l):= fun hx=>by simp [hl hx];
   have ht := oppositeS s h hv; simp only [List.map_cons, passenger,Signed.act_neg] at ht; rw [turn_p, show (seat s) x=s.act x from rfl, ht]; rw [show SideS s ((i,x)::(j,-x)::l)=tick s i * (tick s j*SideS s l) from rfl]; ring_nf; simp only [K,pow_two,tick2,twice_S,mul_one,one_mul]; exact mul_comm .. 
end YM.MS.City
