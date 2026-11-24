import YM.FormalBulk08.Vale.Blots
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
lemma piping {T S: Pot G}(h:Ritual T l)(g:Ritual S r)(a:hue G): Ritual (duplexB T S) (l+r):= by
   have e:=dup_grades h.young g.young; refine ⟨e,spelled T S,fun x E r=>?_,fun n=>?_⟩
   · obtain ⟨s,hs,H⟩:= pledge h x E; obtain ⟨u,hu,Q⟩:= pledge g x E;refine ⟨min s u,?_⟩; obtain ⟨B,hB⟩:= dip_cash (r:=r) (E:=E) (x:=x) (R:=fame _) (p:=T) (q:=S) (fun a ha b=> ⟨_,penn_shrink (H a b ha).choose_spec (min_le_left ..)⟩) (fun a ha b=> ⟨_,penn_shrink (Q a b ha).choose_spec (min_le_right ..)⟩) (lt_min hs hu).le;exact ⟨B,lt_min hs hu,hB⟩
   rw [consumes a h g]; intro I p u b k hv hb hu hk A H q; rw [map_mul,map_mul,h.esteem n I u b k hv hb hu hk A H q,g.esteem n I u b k hv hb hu hk A H q]
-- avoids [Nonempty I]. empty product

def bead (V : Type*): OrbitV V:=fun i r _=> if i+r=0 then 1 else 0
lemma young_bead (l:ℕ)(V : Type*): Young (bead V) l:= fun i r he=> by by_contra hp; unfold Yield at hp; exact he (funext fun x=> if_neg (by omega))
lemma stars_bead (V:Type*)(i r:ℕ): Agate (bead V i r):=fun _ _=> rfl
lemma one_bead [Fintype V]: rancho (1:Pap V)=bead V:= by
   funext e r; rw [rancho,coeff_one]; split
   next h=> subst e; rcases r with (_|r)
            · apply facade_unique (marble_agate _ _) (stars_bead _ _ _)
              rw [marble_grade,MvPolynomial.homogeneousComponent_eq_self, facade_eq]; simp [cards,bead]
              exact MvPolynomial.isHomogeneous_one ..
            have h : marble (r+1) (1:TypeR V)=0:= (marble_eq_zero_iff ..).mpr (by rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_one V ℝ),if_neg (show ¬ r+1=0 by omega)])
            rw [h]; funext; simp [bead]
   next h=> rw [marble_zero]; funext v; symm;exact if_neg (by omega)
lemma ship_bead (m n): Kemp.banner (G:=G) m (bead (edgeL G)) n=1:= by
   apply banner_eq; funext e r; rw [badge (bead _) (young_bead m _) (stars_bead _) le_rfl, one_bead]; funext u
   by_cases h:e+r=0
   · obtain rfl:r=0:= (by omega); obtain rfl:e=0:= (by omega); rw [sieve_i]; simp [bead,Subsingleton.elim _ u]

   simp only [sieve,bead,if_neg h,tsum_zero]
lemma parade (m:ℕ) : Ritual (G:=G) (bead _) m:= by
   refine ⟨young_bead _ _, stars_bead _,fun x e r=>?_,fun n=>?_⟩
   · by_cases h:e+r=0
     · obtain rfl:r=0:= (by omega); obtain rfl:e=0:= (by omega); refine ⟨1,1,one_pos,zero_le_one,?_⟩; simp [Gorge.shine,wide,bead, Reach.self] -- one length
     rw [show bead _ e r=(0:Tile (edgeL G) r) from funext fun _=>if_neg h]; exact ⟨1,_,one_pos,Knox_zeros _⟩
   rw [ship_bead]; intro _ _ _ _ _ _ _ _ _ _ _ _; rw [map_one,map_one]

def packV (f:V→ OrbitV I): List V→ OrbitV I
   | []=>bead I
   | x::l=>duplexB (f x) (packV f l)
lemma pack_cons (f:V→ OrbitV I)(v:List V)(x:V):packV f (x::v)=duplexB (f x) (packV f v):=rfl
lemma pack_one (f:V→ OrbitV I): packV f []=bead I:=rfl
lemma mountV [Fintype I] (f:V→ Pap I)(s:List V): packV (fun i=> rancho (f i)) s=rancho ((s.map f).prod):= by
   induction s with
   | nil=> exact one_bead.symm
   | cons i l ih=> rw [packV,List.map_cons,List.prod_cons,product_read, ih]
lemma orchestra (f:V→Pot G)(l:V→ℕ)(z: List V)(h:∀ i∈z,Ritual (f i) (l i))(a:hue G): Ritual (packV f z) (z.map l).sum:= by
   induction z with
   | nil=>exact parade 0
   | cons i z ih=>exact piping (h _ (List.mem_cons_self)) (ih fun i h'=>h _ (List.mem_cons_of_mem _ h')) a
lemma summons (f : V→Pot G)(l: V→ℕ)(z:List V)(h:∀ i∈z,Ritual (f i) (l i))(a:hue G)(n:Side): Kemp.banner (z.map l).sum (packV f z) n=(z.map fun i=>Kemp.banner (l i) (f i) n).prod:= by
   induction z with
   | nil=> simpa [packV] using (ship_bead (G:=G) 0 n)
   | cons i z ih=> have hp x hx:=h x (List.mem_cons_of_mem _ hx); rw [List.map_cons, List.sum_cons,packV,List.map_cons,List.prod_cons, ←ih hp]; exact consumes a (h i List.mem_cons_self) (orchestra f l z hp a) _
end YM.FormalBulk08.Vale
