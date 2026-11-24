import YM.Contact.PlantBundle

/-! Costs on actual lattice placements for a finite set of jointly tested blocks.
Allow whole families of centers vertically aligned modulo the coarser cell spacing,
with small independent shifts. This also handles period limits taken with the point
reader (later use only at generic finite tuples). -/
noncomputable section
set_option autoImplicit false
namespace YM.MergeProof.Ribbons
open Function Filter Set Lattice Wilson RG Cells Extraction Push Push.RelayDifference MeasureTheory
open scoped BigOperators Topology Classical
variable {G:Gauge}{Q:Schedule}{m l N k p:ℕ}
def strideCount (h:m≤l):ℕ:=(Q.toDepth h 0).count.val -- Q must explicit? includes
lemma count_grid (h:m≤l): (Q.toDepth h p).count.val=strideCount (Q:=Q) h:=by
   have ht:= (Q.embeds_scale (Q.toDepth h p)).trans (Q.embeds_scale (Q.toDepth h 0)).symm
   exact congr_arg PNat.val (show (Q.toDepth h p).count=(Q.toDepth h 0).count from by exact_mod_cast (mul_left_cancel₀ (Q.a_pos l|>.ne') ht))
lemma sparse_enlarge (h:m≤l)(x:Cover) : Q.gridPoint l (strideCount (Q:=Q) h • x)=Q.gridPoint m x :=by
   have hh: Q.a l*(strideCount (Q:=Q) h:ℝ)=Q.a m:=Q.embeds_scale (Q.toDepth h 0)
   ext i; simp only [Schedule.gridPoint, Pi.smul_apply,nsmul_eq_mul,WithLp.ofLp_toLp,Int.cast_mul, Int.cast_natCast]; rw [← mul_assoc,hh] -- norm_cast too much
lemma stride_mul (h:m≤l)(g:l≤N):strideCount (Q:=Q) g * strideCount (Q:=Q) h = strideCount (Q:=Q) (h.trans g):=by
   have hf {a b:ℕ}(h:a≤b): Q.a b * (strideCount (Q:=Q) h:ℝ)=Q.a a:= Q.embeds_scale (Q.toDepth h 0)
   exact_mod_cast (show ((strideCount (Q:=Q) g * strideCount (Q:=Q) h:ℕ):ℝ)=(strideCount (Q:=Q) (h.trans g):ℝ) from by refine mul_left_cancel₀ (Q.a_pos N).ne' ?_; rw [Nat.cast_mul,←mul_assoc,hf g,hf h,hf (h.trans g)])
lemma grid_add (x u:Cover):Q.gridPoint l (x+u)=Q.gridPoint l x+Q.gridPoint l u:=by ext; unfold Schedule.gridPoint; simp [mul_add]
variable {C:Family G}(K:Extraction.Order)
lemma fused_grid (x:Cover) :∀ᶠ u:ℕ×ℕ in K.fuse,C.S.place (m:=u.1) (p:=u.2) (Cells.location C.S l u.1 u.2 x)=C.S.gridPoint l x:=by -- N name? remove
     rw [Order.fused,Order.late]; filter_upwards [K.per.cofinal.eventually (faraway C l x)] with j hj
     filter_upwards [K.mesh.cofinal.eventually (eventually_ge_atTop l)] with n hn
     rw [Cells.location,dif_pos hn, C.S.embeds_place]; exact hj

lemma location_in_grid (h:l≤N)(x:Cover): Cells.location Q l N p x= wrap (Q.side N p) (strideCount (Q:=Q) h • x:Cover):=by
    rw [Cells.location,dif_pos h,Ratio.embed_wrap,count_grid h]
variable (u z p':Cover)
lemma reroute (h:l≤N)(hm:m≤l)(a:Cover)(hu : u=z+(strideCount (Q:=Q) hm:ℕ) • p'+a): Cells.location Q l N p u = Cells.location Q l N p z+ (Q.toDepth (hm.trans h) p).embed (wrap (Q.side m p) p')+wrap (Q.side N p) (strideCount (Q:=Q) h • a:Cover):=by
   simp only [hu, location_in_grid h, smul_add, map_add]; rw [Ratio.embed_wrap,count_grid, smul_smul, stride_mul hm h] -- smul_smul simplifies


variable {I : Type*} [Fintype I] {ρ:I → Cover}{U:∀ (i:I) (N p':ℕ), Config G (C.side N p') →ℂ}
lemma grid_price (β:I→ℝ) (s:I→Bool) (t:I→Signed)(ht:∀ i,diag (t i)) {count:ℕ}(room: (12*(count:ℕ):ℝ)*C.S.a k < C.S.a m)(distances:∀ i j:I,i≠j→2*C.S.a m<‖C.S.gridPoint l (ρ i)-C.S.gridPoint l (ρ j)‖)(hg:m≤k)(hk:k≤l) (a:I → Cover) (u:Fin count → Cover)(v:I → Cover)(idx:I→Fin count)(hr:∀ i,ρ i=u (idx i)+strideCount (Q:=C.S) (hg.trans hk) • v i+a i)(ha:∀ i j,(a i j).natAbs ≤ strideCount (Q:=C.S) hk)
      (hpaid:∀ i,∀ᶠ w:ℕ×ℕ in K.fuse,BlockCost (Q:=C.S) (N:=w.1) (p:=w.2) (U i w.1 w.2) k (C.beta w.1 w.2) (β i))(hC:C.Makes):∀ᶠ w:ℕ×ℕ in K.fuse, ‖moment (C.beta w.1 w.2) (fun V=>∏ i:I, RelayDifference.oriented (U i w.1 w.2) (s i) (t i) (Cells.location (C.S) l w.1 w.2 (ρ i)) V)‖ ≤ ∏ i:I,β i :=by
     have hf:∀ᶠ w:ℕ×ℕ in K.fuse,l≤w.1:=by rw [Order.fused, Order.late]; filter_upwards with j; filter_upwards [K.mesh.cofinal.eventually (eventually_ge_atTop l)] with _ h; exact h
     have hh(i j:I):∀ᶠ w :ℕ×ℕ in K.fuse,C.S.place (Cells.location C.S l w.1 w.2 (ρ i - ρ j))= C.S.gridPoint l (ρ i)-C.S.gridPoint l (ρ j):=by
         filter_upwards [fused_grid (C:=C) K (ρ i-ρ j)] with h hw -- term bind
         rw [hw]; ext l; simp only [Schedule.gridPoint, WithLp.ofLp_toLp,PiLp.sub_apply,Pi.sub_apply, Int.cast_sub, mul_sub]
     filter_upwards [hf,eventually_all.mpr (fun i=>eventually_all.mpr fun j:I=>hh i j),eventually_all.mpr hpaid] with w hN hb hd
     let T:=center C.S w.2 (hg.trans (hk.trans hN)) 0
     let q:=strideCount (Q:=C.S) (hk.trans hN)
     have hq:Cells.span C.S (hk.trans hN) w.2=q:=count_grid _
     have hq0:0<q:=(C.S.toDepth (hk.trans hN) 0).count.property
     apply plant_typed _ _ s t β hd ht (hk.trans hN) hg (Cells.seamless hC w.1 w.2) -- fix
     · intro X hX hU i j h; by_contra hij; set y: I → Site (C.side w.1 w.2):=(fun i=> Cells.location C.S l w.1 w.2 (ρ i))
       have hd0:y i∈X.chamber (X.which (y i))∧y j∈X.chamber (X.which (y i)):=by
           refine ⟨hU i,?_⟩; rw [show X.which (y i)=X.which (y j) from h]; exact hU j
       have hs:=X.extent hd0.1 hd0.2
       have hp := distances i j hij; rw [← hb i j,Cells.location,dif_pos hN,map_sub] at hp
       have h1 := (normC C w.1 w.2 ((y i)-(y j))).2
       have he : C.S.a w.1 * (Cells.span C.S (hg.trans (hk.trans hN)) w.2:ℝ) = C.S.a m := C.S.embeds_scale _ -- params
       rw [hX,separation] at hs; change separation (y i) (y j) ≤_ at hs
       have hmu:=mul_le_mul_of_nonneg_left (show (separation (y i) (y j):ℝ) ≤ ↑(Cells.span C.S _ w.2) from (Nat.cast_le (α:=ℝ)).mpr hs) (le_of_lt (C.S.a_pos w.1))
       rw [show separation (y i-y j) 0=separation (y i) (y j) from by simp [separation]] at h1
       have hy(i):y i=(C.S.toDepth hN w.2).embed (wrap (C.side l w.2) (ρ i)):=by change Cells.location _ _ _ _ _ = _; rw [Cells.location,dif_pos hN]
       have hx:2*C.S.a m< ‖C.S.place ((y i)-(y j))‖:=by
           rw [hy i,hy j,← Ratio.root_embed,← Ratio.root_embed,← map_sub]; exact hp
       linarith
     have hcoord (i:I)(j:Axis): (((strideCount (Q:=C.S) hN) • a i:Cover) j).natAbs ≤ q :=by -- cast wrong
         rw [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; exact (Nat.mul_le_mul_left _ (ha i j)).trans_eq (stride_mul hk hN)
     exact place_together (hk.trans hN) hg (by
            have hr: (center C.S w.2 (hg.trans (hk.trans hN)) 0).side.val=Cells.span C.S (hg.trans (hk.trans hN)) w.2:=rfl
            rw [hr]; refine lt_of_le_of_lt (Nat.mul_le_mul_left _ (show 2*(3*q+q+1)≤12*q by omega)) (?_)
            rw [← hq]; have hR:= C.S.embeds_scale (C.S.toDepth (hk.trans hN) w.2); have hR':= C.S.embeds_scale (C.S.toDepth (hg.trans (hk.trans hN)) w.2)
            have hx:0<C.S.a w.1:=C.S.a_pos _
            have hc1: C.S.a w.1 * ((count*(12*Cells.span C.S (hk.trans hN) w.2):ℕ):ℝ) < C.S.a w.1*(Cells.span C.S (hg.trans (hk.trans hN)) w.2:ℝ):=by
                  rw [hR']; calc
                    _ = (12:ℝ)*count*(C.S.a w.1*↑(Cells.span C.S (hk.trans hN) w.2)):= by push_cast;ring
                    _ = _:= by rw [show C.S.a w.1*↑(Cells.span C.S (hk.trans hN) w.2)=C.S.a k from hR]
                    _ < _ := room
            exact_mod_cast lt_of_mul_lt_mul_left hc1 hx.le) hq.le idx (fun i=>Cells.location C.S l w.1 w.2 (u i)) (wrap (C.side m w.2)∘v) (fun i=> strideCount (Q:=C.S) hN • a i) (fun i=>reroute (Q:=C.S) (u:=ρ i) (z:=u (idx i)) (p':=v i) hN (hg.trans hk) _ (hr i)) hcoord
end YM.MergeProof.Ribbons
