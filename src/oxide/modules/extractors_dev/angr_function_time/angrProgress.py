class angrProgress:
    """ Display progress through functions of an oid
    """
    def __init__(self, lot: int = 1) -> None:
        self.lot = lot
        self.progress = 0
        self.length = 50

    def tick(self) -> None:
        self.progress+=1
        prog = int(round((self.progress/self.lot)*self.length)-1)
        print(f"Function progress: [{'='*prog + ' '*(self.length-int(round((self.progress/self.lot)*self.length)-1))}] {self.progress}/{self.lot}",flush=True,end="\r")
        
        if self.progress/self.lot == 1:
            print()
