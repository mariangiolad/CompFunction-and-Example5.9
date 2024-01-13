

-- ===== Participants, Interactions and Messages ======

data Participant =  Participant String
 deriving (Eq)

instance Show Participant where
     show (Participant s) = s


data Interaction = Interaction Participant Participant
  deriving (Eq)

instance Show Interaction where
     show (Interaction p1 p2) = (show p1)++"->"++(show p2)


data Message =  Message String
 deriving (Eq)

instance Show Message where
     show (Message s) = s



--  ==== GlobalTypes ==============

data GlobalType = End 
                 | MkGT Interaction [(Message,GlobalType)] 
                 | Cut -- represents a "pruned away" subterm (needed when showing a pruned global type) 

instance Show GlobalType where
     show gt = showd 0 gt
           where
               showd n End = "End"
               showd n Cut = "ETC."
               showd n (MkGT inter [])       = "malformed type"
               showd n (MkGT inter [(l,gt)]) = (show inter)++" : "++(show l)++". "++(showd (n+(lenint inter)+(lenmes l)+(if (n==0) then 4+(lenmes l) else 6)) gt)
               showd n (MkGT inter ls)          = (show inter)++" : {"++"\n"++(showlist (n+(lenint inter)) ls)++"}" 
               showlist n [(l,gt)]     = (blanks n)++(show l)++". "++(showd n gt)
               showlist n ((l,gt):xs)  = (blanks n)++(show l)++". "++(showd n gt)++",  "++"\n"++(showlist n xs)
               

-- some auxiliary functions ---

blanks :: (Eq t, Num t) => t -> [Char] -- returns a string of n blanks 
    
blanks 0  = ""
blanks n  = " "++(blanks (n-1))

lenint :: Interaction -> Int          -- returns the lenght of the string representation of an interaction
lenint (Interaction (Participant s1) (Participant s2)) = (length s1)+(length s2)+2

lenmes :: Message -> Int              -- returns the lenght of the string representation of a message
lenmes (Message s) = (length s)

lenp :: Participant -> Int            -- returns the lenght of the string representation of a participant
lenp   (Participant s) = (length s)


-- ------ The function prune -----------

prune :: (Eq t, Num t) => t -> GlobalType -> GlobalType      -- cut the branches of a a global type at level n

prune 0 gt   = Cut

prune n End = End

prune n (MkGT inter xs)    = (MkGT inter (pruneaux (n-1) xs)) 
                   where
                        pruneaux n []    = []
                        pruneaux n ((l,gt):xs) = (l,(prune n gt)):(pruneaux n xs)


-- ======= Processes =======================

data Process =  Inact 
              | Mkinput Participant [(Message, Process)] 
              | MkOutput Participant [(Message, Process)]
    deriving (Eq)


instance Show Process where
     show proc = showdp 0 proc
        where
             showdp n Inact = "Inact"
             showdp n (Mkinput p [])          = "malformed process"
             showdp n (MkOutput p [])         = "malformed process"
             showdp n (Mkinput p [(m,proc)])  = (show p)++"?"++(show m)++"."++(showdp (n+(lenp p)+(lenmes m)+(if (n==0) then 3 else 5)) proc)
             showdp n (MkOutput p [(m,proc)]) = (show p)++"!"++(show m)++"."++(showdp (n+(lenp p)+(lenmes m)+(if (n==0) then 3 else 5)) proc)
             showdp n (Mkinput p ls)  = (show p)++"?"++"{"++"\n"++(showlistp (n+2+(lenp p)) ls)++"}"
             showdp n (MkOutput p ls) = (show p)++"!"++"{"++"\n"++(showlistp (n+2+(lenp p)) ls)++"}"
             showlistp n [(m,proc)]     = (blanks n)++(show m)++". "++(showdp n proc)
             showlistp n ((m,proc):xs)  = (blanks n)++(show m)++". "++(showdp n proc)++","++"\n"++(showlistp n xs)


                                     
-- ========== compliance judgments ======

data Judgment = Judgment Process Process Process
        deriving (Eq)
 
instance Show Judgment where
     show (Judgment proc1 proc2 proc3) = (show proc1)++" |- <"++(show proc2)++" , "++(show proc3)++">"

-- ------ some judgments --------------

judgtest =  (Judgment h1 h2 h3)

-- ======== derivations =============

data Derivation =  Comp0 Judgment 
                 | CompOIL [Derivation] Judgment 
                 | CompIOL [Derivation] Judgment 
                 | CompOIR [Derivation] Judgment 
                 | CompIOR [Derivation] Judgment 
                 | CompOIA [Derivation] Judgment 
                 | CompIOA [Derivation] Judgment 
     deriving (Eq,Show)



-- --------- composition function ---------

g :: Derivation      
     -> GlobalType
     -> GlobalType
     -> GlobalType
     -> Participant
     -> Participant
     -> Participant
     -> GlobalType
-- function g implements the function G defined in the proof of Theorem 5.8 
-- (the arguments ph, pv and ph are the name of interfaces names left implicit in the theorem)

g (Comp0 judg) gt1 gt2 gt3 ph pv pw  = gt1

g d@(CompOIL derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2@(MkGT (Interaction p3 p4) mglist2) gt3 ph pv pw  
 | (p1,p4) == (ph,pv) = let 
                                    (ms,gts2)   = (unzip mglist2)
                                    (_,gts1aux) = (unzip mglist1)
                                    gts1        = (take (length gts2) gts1aux)
                                    rcalls      = [(g di gi ggi gt3 ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts2)] 
                                    hatgts      = [(MkGT (Interaction pv ph)  [(m, (MkGT (Interaction ph p2) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p3 p4) (zip ms hatgts))
  
 
 | (p1==ph)          = let           
                                   (ms,gts2)   = (unzip mglist2)
                                   rcalls      = [(g d gt1 gi gt3 ph pv pw) | gi<- gts2]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompIOL derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2@(MkGT (Interaction p3 p4) mglist2) gt3 ph pv pw  
 | (p2,p3) == (ph,pv) = let 
                                    (ms,gts1)   = (unzip mglist1)
                                    (_,gts1aux) = (unzip mglist2)
                                    gts2        = (take (length gts1) gts1aux)
                                    rcalls      = [(g di gi ggi gt3 ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts2)] 
                                    hatgts      = [(MkGT (Interaction ph pv)  [(m, (MkGT (Interaction pv p4) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p1 p2) (zip ms hatgts))
  
 
 | (p2==ph)          = let           
                                   (ms,gts2)   = (unzip mglist2)
                                   rcalls      = [(g d gt1 gi gt3 ph pv pw) | gi<- gts2]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompOIR derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3@(MkGT (Interaction p3 p4) mglist3) ph pv pw  
 | (p1,p4) == (ph,pw) = let 
                                    (ms,gts3)   = (unzip mglist3)
                                    (_,gts1aux) = (unzip mglist1)
                                    gts1        = (take (length gts3) gts1aux)
                                    rcalls      = [(g di gi gt2 ggi ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts3)] 
                                    hatgts      = [(MkGT (Interaction pw ph)  [(m, (MkGT (Interaction ph p2) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p3 p4) (zip ms hatgts))
  
 
 | (p1==ph)          = let           
                                   (ms,gts3)   = (unzip mglist3)
                                   rcalls      = [(g d gt1 gt2 gi ph pv pw) | gi<- gts3]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompIOR derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3@(MkGT (Interaction p3 p4) mglist3) ph pv pw  
 | (p2,p3) == (ph,pw) = let 
                                    (ms,gts1)   = (unzip mglist1)
                                    (_,gts3aux) = (unzip mglist3)
                                    gts3        = (take (length gts1) gts3aux)
                                    rcalls      = [(g di gi gt2 ggi ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts3)] 
                                    hatgts      = [(MkGT (Interaction ph pw)  [(m, (MkGT (Interaction pw p4) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p1 p2) (zip ms hatgts))
  
 
 | (p2==ph)          = let           
                                   (ms,gts3)   = (unzip mglist3)
                                   rcalls      = [(g d gt1 gt2 gi ph pv pw) | gi<- gts3]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompOIA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))


g d@(CompIOA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

-- ========== EXAMPLE 5.9 ===========

-- participants in the example -------------------------

p = (Participant "p")
r = (Participant "r")
s = (Participant "s")
q = (Participant "q")
nh = (Participant "h")
nv = (Participant "v")
nw = (Participant "w")

--  interactions in th eexample ----------------------------

htop = Interaction (Participant "h") (Participant "p")
ptoh = Interaction (Participant "p") (Participant "h")
stov = Interaction (Participant "s") (Participant "v")
wtor = Interaction (Participant "w") (Participant "r")
rtow = Interaction (Participant "r") (Participant "w")

---- messages in the example ---------------------------

reactn = (Message "reactn")
img    = (Message "img")
start  = (Message "start")
halt   = (Message "halt")
go     = (Message "go")
stop   = (Message "stop")

-- global types in the example -------------------

g1pp = MkGT ptoh [((Message "reactn"),(MkGT htop [((Message "img"),g1)]))]
g1p = MkGT htop [((Message "img"),g1pp),((Message "halt"),End)]

g1  = MkGT htop [((Message "start"),g1p)]
g2  = MkGT stov [((Message "img"),g2),((Message "halt"),g2)]
g3 = MkGT wtor [((Message "reactn"),(MkGT rtow [((Message "img"),g3)]))]

-- the processes in the example ------------

h3 = (MkOutput p [(img,Inact)])
h2 = (Mkinput p [(reactn,h3)])
h1 = (MkOutput p [(img,h2),(halt,Inact)])
h  = (MkOutput p [(start,h1)])

v  = (Mkinput s [(img,v),(halt,v)])

w1 = (Mkinput r [(img,w)])
w  = (MkOutput r [(reactn,w1)])

-- -------- the compliance derivation in the example -------------------

der1 = (Comp0 (Judgment Inact v w)) -- applyComp0 v w
der2 = (CompIOR [(CompOIR [der] (Judgment h3 v w1))] (Judgment h2 v w))
der3 = (CompOIL [der2,der1] (Judgment h1 v w))

der = (CompOIA [der3] (Judgment h v w))


-- The (infinite) global type that can be obtained by composing g1, g2 and g3 is hence
--                        (g der g1 g2 g3 nh nv nw)
-- whose cut at level, say, 10 can be obtained by evaluating
--            prune 10 (g der g1 g2 g3 nh nv nw)
-- getting
-- h->p : start. s->v : {
--                       img. v->h : img. h->p : img. p->h : reactn. h->w : reactn. w->r : reactn. r->w : img. w->h : img. h->p : img. ETC.,
--                       halt. v->h : halt. h->p : halt. End}


