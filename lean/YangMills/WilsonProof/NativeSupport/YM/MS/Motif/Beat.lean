import YM.MS.Motif.Beat
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Channel
/-!
# Hamiltonian of seed log action from point BV functional Ward

Total bracket of even, vertical shot and translate ∫.D0.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment
open scoped Topology ContDiff
variable {A:Type}{G:Gauge}{n:ℕ} {F H:Rack G n} {b c:Bool} {k:Chan G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
lemma swap (p:Sector A)(l:Legs A)(K:Shared A ℂ): scatter p l K=scatter p l (fun x y=> cross (degree p x) (degree p y)*K y x) := by
   induction l generalizing K with
   | nil=> simp
   | cons i l ih=> rw [scatter_cons, ih,scatter_cons]; apply scatter_congr; intro a b hz; cases hv: p i <;> cases ha: degree p a <;> cases hb: degree p b <;> simp [*,Bool.xor] <;> abel
-- both even ⇒ true has anti on right; equal to false orientation on Course after swapping
lemma pearl (hF: Pure S false F) (hh: Pure S false H) (l:Legs (Shore G n))(he:net l=0): shoots true F H l=shoots false H F l:= by
   unfold shoots; simp_rw [ LinearMap.sum_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [quamped,quamped]; unfold tip; rw [swap]; apply scatter_congr; intro a b hp; have hN: net a + net b=0:= (split_net hp).trans he; let x:= onX true i; let y:= onX false i;
   have ht: degree S a≠parity x→ H ((x,net b)::a)=0:= fun hz=> hh _ (degree0 hz _)
   have hv: degree S b≠parity y→ F ((y,net a)::b)=0:= fun hz=> hF _ (degree0 hz _)
   change cross (degree S a) (degree S b) * (phase i * F ((y,-net b)::b)*H ((x,net b)::a))= phase i * H ((x,-net a)::a)*F ((y,net a)::b); rw [neg_eq_iff_add_eq_zero.mpr (by rwa [add_comm]), show -net a=net b from neg_eq_iff_add_eq_zero.mpr hN]; by_cases ha: degree S a=parity x; swap; · rw [ht ha]; ring
   by_cases hb:degree S b=parity y; swap; · rw [hv hb]; ring
   have hl:parity x= !(parity y):= phase_par i; rw [ha,hb,hl]; cases hy:parity y <;> simp <;> ring
where degree0 {v:Cfield G n}{l:Legs (Shore G n)}(h:degree S l≠ parity v)(s:SectorP n): degree S ((v,s)::l)≠false := by rw [degree_cons]; change (parity v ^^ degree S l)≠false; cases he: degree S l <;> cases hr: parity v <;> simp only [he,hr] at h <;> first| decide| contradiction
-- unstar test
lemma shoots_off (h:fieldSection b F) : shoots (!b) H F=0:= by
    funext l; simp_rw [shoots,LinearMap.sum_apply,Finset.sum_apply]; refine Finset.sum_eq_zero fun a _=>?_ ; unfold quash tip; dsimp only [LinearMap.mk₂_apply]; simp_rw [ show ∀ i l,F ((onX (!b) a,i)::l)=0 from fun i l=> congr_fun (h a i) l,mul_zero]; exact map_zero (allocate .. )
-- handy qhoriz $∂Rank Shape$.
-- letter at point
local infixl:67 "⋄"=> product S
variable {v:Chan G n→ Rack G n}(hv:Lamp v)
include hv
lemma cape_tick (i:Chan G n)(x:SectorP n): D (onX true i,x) (cape v)=phase i • v i:= by
   unfold cape; simp_rw [map_sum,map_smul,D_product, show ∀ j,D (onX true i,x) (v j)=0 from fun j=> hv.onlyA j i x,map_zero,add_zero,leaf,nodeD,onXC]; simp only [coin_product]; simp
lemma cape0 : Pure S false (cape v):= by
   refine Pure.sum _ fun i hi=> Pure.smul _ ?_; obtain hx:= Pure.prod (p:=S) ( note_p (onX true i) (fun (_:SectorP n)=> (1:ℂ))) (hv.being i); simpa only [phase_par, Bool.true_xor, Bool.xor_self] using hx
lemma pulse (h:fieldSection false F): shoots false (F+cape v)=dot v:= by
    have hx (i:Chan G n): glow0 false (F+cape v) i=v i:= by funext l; change phase i * D (onX true i,-net l) ( F+cape v ) l=_; rw [map_add,show D (onX true i, -net l) F=0 from h i (-net l),zero_add,cape_tick hv,Pi.smul_apply,smul_eq_mul,← mul_assoc,phase2,one_mul]
    unfold dot shoots; simp_rw [hx]
omit hv in
lemma dot_never (a:Chan G n): dot v (leaf (onX true a))=0:= by
    unfold dot; funext l; simp_rw [LinearMap.sum_apply,Finset.sum_apply,leaf,note_q]; simp [onX]
lemma constitution (hF:Pure S false F)(hs:fieldSection false F)(hp:dot v F=0)(ht:∀ i,dot v (v i)=0) {l:Legs (Shore G n)} (hr:net l=0): tree parity (Wick.D0 G n) (F+cape v) ( F+cape v ) l=0:= by
    obtain H := hF.add (cape0 hv); rw [hearth H,Pi.add_apply,pearl H H l hr,pulse hv hs,map_add,hp,zero_add]; unfold cape; simp_rw [map_sum,map_smul,dot_pair hv ((show ∀ i, Pure S (parity ( onX true i )) (leaf (onX true i)) from fun i=> note_p ( onX true i ) _) _), ht,dot_never]; simp; -- patch `.apply`
end YM.MS.Motif
