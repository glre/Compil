type fonction = {id : int list;
                 nom : string;
                 pilesauv : int; pileio : int; pilers : int; pilerv : int; piletab : int;
                 nbEntParam : int;
                 nbTablParam : int;
                 tab : int array;
                 corps : Ast4.instruction list}



type programme = {tableauConsEnt : (int array) array; tableauString : string array; principal : (int list,(fonction*string)) Hashtbl.t}


