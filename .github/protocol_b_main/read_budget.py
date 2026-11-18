"""One-stage read budget and request cache; no retry of writes or unknown reads."""
import copy


class ReadBudgetExceeded(RuntimeError):pass


class BoundedReads:
    def __init__(self,api,limit=60):
        if type(limit) is not int or not 1<=limit<=100:raise ValueError('read budget')
        self.api=api;self.limit=limit;self.count=0;self.cache={}
    @property
    def remaining(self):return self.limit-self.count
    def _read(self,kind,path):
        key=(kind,path)
        if key in self.cache:return copy.deepcopy(self.cache[key])
        if self.count>=self.limit:raise ReadBudgetExceeded('Recovery read budget exhausted; retain pending work')
        self.count+=1
        value=getattr(self.api,kind)(path)
        self.cache[key]=copy.deepcopy(value)
        return value
    def json(self,path):return self._read('json',path)
    def bytes(self,path):return self._read('bytes',path)
    def fresh(self):self.cache.clear()
    def post_once(self,path,data):return self.api.post_once(path,data)
