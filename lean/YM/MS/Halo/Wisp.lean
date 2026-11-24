import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Alpha
/-!
# Rack degrees, heat signature at any sector dimension
Used for classical starting terms in MS pole scheme. Includes cap uniform rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Alps
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {m n k h j:ℕ}{b:Bool}{s t r q p:ℤ}{z:ℂ}{X F H: Rack G n}{U Y:Mield G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex) )
local infixl:68 "⋄"=> product S
structure Pace (X: Rack G n)(h:ℕ)(t r:ℤ): Prop where
   price : ∀ E:Type, [NormedAddCommGroup E]→ [NormedSpace ℝ E]→ [FiniteDimensional ℝ E]→  ∀ w:Wire ( Cfield G n ) E ( SectorP n ), veg 0 (fun _:Unit=> fieldVal X w) 1
   home (l:Legs ( Shore G n )) (x:ℝ) : amount (-(h:ℂ)+(mass l:ℂ)) x* X (sr x l)=X l
   sym : Symm S X -- name binder n used?
   ghost : Rails ( ghostNo ∘ Prod.fst ) t X
   sense (l:Legs ( Shore G n )) : X (invertMom l)=star (X l)
   up: Limit X r
lemma stanza (c:ℂ){E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]: veg 0 (fun (_:Unit) (_:E)=> c) 1:= at_rate (const_sc (z:=0) _)
lemma stampX {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g:E→ℂ} (h: veg 0 (fun _:Unit=> f) 1) (he:veg 0 (fun _:Unit=>g) 1) : veg 0 (fun (_:Unit) p=> f p * g p) 1 := by convert! Costs.mul h he using 1; ext; simp
namespace Pace
lemma zero : Pace (0:Rack G n) h t r:= ⟨fun _ _ _ _ _=> Costs.zero fun _ _ _=>zero_le_one,fun _ _=>mul_zero _, Symm.zero, Rails.zero, fun _=>star_zero ℂ|>.symm, fun _ _=>rfl⟩
-- orientation
lemma plus (hF:Pace F h t r)(ht:Pace X h t r): Pace (F+X) h t r:=⟨ fun E i j k w=> Costs.add (hF.price E w) (ht.price E w),fun l v=> by rw [Pi.add_apply,mul_add,hF.home,ht.home,Pi.add_apply], hF.sym.add ht.sym,hF.ghost.add ht.ghost,fun l=>by rw [ Pi.add_apply,hF.sense,ht.sense,Pi.add_apply,star_add], hF.up.add ht.up⟩ -- implicit binder i j class arrows? lemma elaborates.
lemma cash (hF:Pace F h t r)(ht: star z=z): Pace (z • F) h t r:= ⟨fun E i j k w=>(hF.price E w).L (ContinuousLinearMap.mul ℝ ℂ z),fun l v=> by simp only [Pi.smul_apply,smul_eq_mul]; rw [mul_left_comm,hF.home], hF.sym.smul _,hF.ghost.smul _,fun l=> by simp only [Pi.smul_apply,hF.sense,smul_eq_mul,star_mul',ht], hF.up.smul _⟩
lemma minus (hF:Pace F h t r)(ht:Pace X h t r): Pace (F-X) h t r:= by simpa only [neg_one_smul,sub_eq_add_neg] using hF.plus (ht.cash (z:=(-1)) (by simp))
lemma total {F:J→ Rack G n}(A:Finset J)(he:∀ i∈A,Pace (F i) h t r): Pace (∑ i∈A,F i) h t r:= by classical induction A using Finset.induction with| empty=>rw [Finset.sum_empty]; exact Pace.zero|insert i a hi ih=>rw [ Finset.sum_insert hi]; exact (he i (by simp)).plus (ih fun t ht=> he t (by simp [ht]))
lemma taller (he:Pace F h t r)(hx:r≤q): Pace F h t q:= { he with up := he.up.up hx }
lemma times (hF:Pace F h t r)(hx:Pace X k p q): Pace (F⋄ X) (h+k) (t+p) (r+q):= by
   refine ⟨ ?_,?_,hF.sym.times hx.sym,hF.ghost.product hx.ghost,?_,hF.up.pair hx.up⟩
   · intro E _ _ _ w; unfold fieldVal; simp only [scattered,sail_scatter]; apply gather_bound w; intro l v _; exact stampX (hF.price E l) (hx.price E v)
   · intro l v; let c:=amount (-((h+k:ℕ):ℂ) +(mass l:ℂ)) v; simp_rw [scattered]; rw [scatter_sr]; refine ( map_smul (allocate S l) c (fun i j=> F (sr v i)*X (sr v j))).symm.trans (scatter_congr _ _ _ _ (fun i j he=>?_)); change c* (F (sr v i) *X (sr v j))=_; unfold c; rw [show amount _ v =amount ( -(h:ℂ)+mass i) v*amount (-(k:ℂ)+mass j) v from Eq.symm ?ein, mul_mul_mul_comm,hF.home,hx.home]; case ein=> rw [← amount_add, ← price_mag_split he]; push_cast; congr 1; ring
   intro w; rw [scattered,scattered,aqua]; simp only [hF.sense,hx.sense,star_mul',star_star]
lemma seek (a:Arts.L n)(hF:Pace F h t r): Pace (rowP a F) (h+1) t r := by
   unfold rowP; refine ⟨?_,?_,m_sp hF.sym _,(fun i hi=>by rw [moon,hF.ghost i hi,mul_zero]),?_,fun l hl=>by rw [moon, hF.up _ hl, mul_zero]⟩
   · intro E _ _ _ w; unfold fieldVal; simp_rw [moon, sail_net,spike_δ]; apply stampX _ (hF.price E w); exact Costs.L ((ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (φ:=fun _:Arts.L n=>ℝ) a).comp ( net w )) )) ( Bench.Forest.at_id (E:=E))
   · intro l v; rw [moon,moon, net_sr, spike_δ,spike_δ]; change amount _ v*( Complex.I * ( (exp v*(net l a):ℝ):ℂ) * _ )=_; have hv:amount (-((h+1:ℕ):ℂ)+(mass l:ℂ)) v = (exp v :ℂ)⁻¹ * amount ( -(h:ℂ)+ (mass l:ℂ)) v := by rw [ show -((h+1:ℕ):ℂ)+ (mass l:ℂ)= (-1)+ ( -(h:ℂ)+( mass l:ℂ)) from by push_cast; ring, amount_add]; simp [amount,Complex.ofReal_exp,Complex.exp_neg]; -- factor nonce
     rw [hv]; push_cast; rw [← hF.home l v]; unfold spikeV; field_simp
   intro l; simp_rw [moon,net_invert,hF.sense,spike_δ]; simp [spikeV]
lemma here (a:Cfield G n): Pace (Motif.leaf a) ( Landau.dim a.1) (ghostNo a) 1:= by
   refine ⟨?_,?_, note_sym a _, ?_, ?_, fun l hl=> mon_leaf a l (by rw [mod_int]; omega)⟩
   · intro E _ _ _ l; rcases l with _|⟨w,_|u⟩ <;> first| exact stanza (E:=E) (0:ℂ)| exact stanza (E:=E) (if w.1=a then 1 else 0)
   · intro w x; rcases w with _|⟨i,_|s⟩; exact mul_zero _; · simp only [sr,List.map_cons,List.map_nil,Motif.leaf,node1]; split; rename_i hw; rw [Price_cons (i:=i),hw]; simp [mass,amount,wfield]; simp only [mul_zero]
     exact mul_zero _
   · intro l hl; rcases l with _|⟨i,_|s⟩; exacts [rfl,if_neg fun hx=> hl (by simp [hx]),rfl]
   intro l; rcases l with _|⟨i,_|s⟩; exact (star_zero ℂ).symm; simp [Motif.leaf,invertMom,node1]; exact (star_zero ℂ).symm
lemma unit : Pace (coin (1:ℂ): Rack G n) 0 0 0:= by
    refine ⟨?_,?_, coin_symm _, Rails.coin _,?_,?_ ⟩ -- names
    · intro E _ _ _ w; rcases w with _|_ <;> exact stanza _
    · intro l v; rcases l with _|_; simp [amount,coin,mass,sr]; exact mul_zero _
    · intro l; rcases l with _|_; simp [coin,invertMom]; exact star_zero ℂ |>.symm
    intro l hl; rcases l with _|_; simp at hl; rfl
end Pace
end YM.MS.Halo
