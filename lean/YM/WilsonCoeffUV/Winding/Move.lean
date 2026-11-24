import YM.WilsonCoeffUV.Winding.RootKernel
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type*}{i j k r:ℕ}{s a A B C t q :ℝ}
variable {F:ropes Cover α β}{P:ropes (Site n) α β}
structure Rail (P: ropes (Site n) α β)(F: ropes Cover α β)(s A:ℝ):Prop where
   bow : dragCup (tor n) s A P
   berth : dragCup Bank.terrain s A F
   far (x y):4*Bank.terrain.gap x.1 y.1<n.val→ ‖P (foldUnder n x) (foldUnder n y)-F x y‖ ≤ A*catchW s n
   haul : hauling P
lemma Rail.mono (h:Rail P F s A)(p:t≤s): Rail P F t A:=⟨h.bow.mono p,h.berth.mono p,fun x y v=> (h.far x y v).trans (mul_le_mul_of_nonneg_left (catch_width p n) h.bow.1),h.haul⟩
lemma Rail.more (h:Rail P F s A)(p:A≤B): Rail P F s B:=⟨h.bow.le p,h.berth.le p,fun x y v=>(h.far x y v).trans (mul_le_mul_of_nonneg_right p (catch_hot ..)),h.haul⟩
lemma Rail.zero : Rail (0: ropes (Site n) α β) 0 s 0:=⟨dragCup.zero,dragCup.zero,by simp,fun _ _ _=>rfl⟩
lemma Rail.unit [DecidableEq α] : Rail (1:ropes (Site n) α α) 1 s 1:=by
   refine ⟨dragCup.one,dragCup.one,?_, by intro b x y; simp [Matrix.one_apply]⟩; intro x y h
   have hp: foldUnder n x=foldUnder n y ↔ x=y:=by
       refine ⟨fun e=>Prod.ext ?_ (show (foldUnder n x).2=(foldUnder n y).2 from congr_arg Prod.snd e),congr_arg _⟩
       have he:wrap n x.1=wrap n y.1:= congr_arg Prod.fst e
       have ht:= nearTau (x:=x.1) (y:=y.1) (n:=n) (by omega); rw [he] at ht; exact (sub_eq_zero.mp (by simpa using ht.symm)).symm
   simp [Matrix.one_apply,hp,catch_hot]
lemma Rail.spin (h:Rail P F s A): Rail P.transpose F.transpose s A:=by
   refine ⟨⟨h.bow.1,fun x y=>?_⟩, ⟨h.berth.1,fun x y=>?_⟩,fun x y v=>h.far y x (by rwa [Bank.terrain.swap _ _] at v), fun b x y=> h.haul b y x⟩
   · rw [(tor n).swap _ _]; exact h.bow.2 y x
   rw [Bank.terrain.swap _ _]; exact h.berth.2 y x
lemma Rail.upperL {P:ropes (Site n) α α}{F:ropes Cover α α}{Q:ropes (Site n) α β}{G:ropes Cover α β}(h:Rail P F s A)(p:Rail Q G s A): Rail (upper P Q) (upper F G) s A:= ⟨by simpa using upper_cap h.bow p.bow,by simpa using upper_cap h.berth p.berth,by rintro i ⟨x,h|h⟩ b; exacts [Rail.far ‹Rail P F s A› i (x,h) b,p.far i (x,h) b],by rintro b i ⟨x,t|t⟩; exacts [h.haul b i (x,t),p.haul b i (x,t)]⟩
lemma Rail.stairL {P:ropes (Site n) α ι}{F:ropes Cover α ι}{Q:ropes (Site n) β ι}{G:ropes Cover β ι}(h:Rail P F s A)(p:Rail Q G s A): Rail (stair P Q) (stair F G) s A:= ⟨by simpa using strafe h.bow p.bow,by simpa using strafe h.berth p.berth,by rintro ⟨x,b|b⟩ i v; exacts [h.far (x,b) i v,p.far (x,b) i v],by rintro b ⟨x,t|t⟩ i; exacts [h.haul b (x,t) i,p.haul b (x,t) i]⟩
lemma Rail.ladderL [DecidableEq β] : Rail (ladder (U:=Site n) (α:=α) (β:=β)) ladder s 1 := by
   let h:= Rail.unit (n:=n) (α:=β) (s:=s)
   refine ⟨ladder_amber,ladder_amber,?_,by rintro x i ⟨y,h|h⟩; rfl; exact (Rail.unit (n:=n) (α:=β) (s:=s)).haul x i (y,h)⟩
   rintro i ⟨j,b|b⟩ p
   · change ‖(0:ℝ)-0‖ ≤ _; rw [sub_self,norm_zero,one_mul]; exact catch_hot ..
   exact h.far i (j,b) p
lemma Rail.bruise {P:ropes (Site n) α α}{F:ropes Cover α α}(h:Rail P F s A): Sight (orbQ P) (orbQ F) s A:=by
   refine ⟨by rw [pruce_down]; exact drag_orb h.bow,drag_orb h.berth, ⟨h.bow.1,fun x v=> ?_⟩,fun b x=> congr_arg (·/2) (h.haul b (x 0) (x 1))⟩
   rw [drag_two] at v; have hv:=h.far (x 0) (x 1) v; change _ ≤ _; rw [pruce_down]; change ‖(_/2:ℝ)-_/2‖≤_; rw [← sub_div,norm_div]; exact (div_le_self (by positivity) (by norm_num)).trans hv
lemma boarding [Fintype β] (F:Row α β)(h:F.strip s A)(p:0<s)(x:0≤A): Rail (F.acts n) (shuttleM F) (s/8) ((Fintype.card β+1)*Real.exp s*A):=by
   set w:= n.val/4
   let b:ℝ:= Fintype.card β; let B:=(b+1)*Real.exp s*A; have hb:0≤ b:=by unfold b; positivity
   have hh: 1≤Real.exp s:= Real.one_le_exp p.le
   have hp: b*A≤ B:= by change _≤ (b+1)*_*A; gcongr; nlinarith
   have hg:A≤ B:=by change _≤_ * A; apply le_mul_of_one_le_left x; nlinarith
   have he: dragCup (tor n) s (b*A) (F.acts n):=by refine ⟨mul_nonneg hb x,fun i j=>?_⟩; rw [mul_comm]; exact (physical_rows h p.le n).point i j
   refine ⟨(he.le hp).mono (by linarith), ((matrix_width h x).le hg).mono (by linarith),?_,?_⟩
   · intro i j v
     have hu:= n.property
     have hv:= lift_comparison h p.le (wrap n i.1) (j.1-i.1) i.2 j.2 w (show _≤w from by change 4*size (j.1-i.1)<n.val at v; unfold w; omega) (show _ from by unfold w; omega)
     rw [map_sub,add_sub_cancel] at hv
     change _ ≤ B*_
     apply le_trans hv; change b*(Real.exp (-s*w)*A) ≤ B*catchW _ n.val; have ht:(n.val:ℝ)≤4*w+4:=by exact_mod_cast (show n.val≤4*w+4 from by unfold w; omega)
     have hz: Real.exp (-s*w)≤ Real.exp s * catchW (s/8) n:=by
         unfold catchW; rw [← Real.exp_add,Real.exp_le_exp]; nlinarith [mul_le_mul_of_nonneg_left ht p.le]
     apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz x) hb); unfold B; have hw:= catch_hot (s/8) n
     rw [show b*(_*A)= b*Real.exp s*A*catchW (s/8) n from by ring]; gcongr; linarith
   intro b x y; refine tsum_congr fun z=>?_; congr 1; ext; simp [jog,add_assoc]
end YM.WilsonCoeffUV.Winding
